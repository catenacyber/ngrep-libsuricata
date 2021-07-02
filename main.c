// Copyright (c) 2021 Catena cyber
// Author Philippe Antoine <p.antoine@catenacyber.fr>



#include <pcap/pcap.h>

#include <hs/hs.h>

#include <suricata.h>
#include <tm-modules.h>
#include <tmqh-packetpool.h>
#include <pkt-var.h>
#include <util-profiling.h>
#include <stream-tcp.h>
#include <flow-hash.h>
#include <flow-storage.h>
#include <app-layer.h>

SCInstance surifuzz;
void *fwd; //FlowWorkerData
ThreadVars tv;
DecodeThreadVars *dtv;
static FlowStorageId g_flow_storage_ngrep_id = { .id = -1 };
hs_scratch_t *scratch_stream;
hs_database_t *hs_db_stream = NULL;

extern libsuricata_tcp_cb AppLayerTCPDataCallback;

#define NGREP_RINGBUFFER_SIZE 0x1000 // 4096

typedef struct NgrepStorageStream {
    hs_stream_t *hstr;
    uint8_t buffer[NGREP_RINGBUFFER_SIZE];
    uint32_t end;
    uint8_t *data;
    uint32_t data_len;
    uint32_t last;
} NgrepStorageStream;

typedef struct NgrepStorageStreams {
    NgrepStorageStream toc;
    NgrepStorageStream tos;
} NgrepStorageStreams;


static uint32_t NgrepPrint(uint8_t *data, uint32_t data_len, uint32_t from, uint32_t to) {
    uint32_t start = to;
    while (start > 0) {
        if (data[start] == '\n' || data[start] == '\r') {
            start++;
            break;
        }
        start--;
    }
    uint32_t end = to;
    while (end < data_len) {
        if (data[end] == '\n' || data[end] == '\r') {
            break;
        }
        end++;
    }
    for (uint32_t i = start; i < end; i++) {
        if (data[i] == '%') {
            printf("%%%02x", data[i]);
        } else if (isprint(data[i])) {
            printf("%c", data[i]);
        } else {
            printf("%%%02x", data[i]);
        }
        
    }
    printf("\n");
    return end;
}

static uint32_t NgrepRingPrint(NgrepStorageStream *ns, uint32_t to) {
    if (ns->data_len > NGREP_RINGBUFFER_SIZE) {
        // use just last big buffer
        uint32_t r = NgrepPrint(ns->data, ns->data_len, 0, to + ns->data_len - ns->end);
        return r + ns->end - ns->data_len;
    }
    // else use ring buffer
    uint32_t start = to % NGREP_RINGBUFFER_SIZE;
    while (start != ns->end % NGREP_RINGBUFFER_SIZE) {
        if (ns->buffer[start] == '\n' || ns->buffer[start] == '\r') {
            start = (start + 1) % NGREP_RINGBUFFER_SIZE;
            break;
        }
        start = (start - 1) % NGREP_RINGBUFFER_SIZE;
        if (start == 0 && ns->end < NGREP_RINGBUFFER_SIZE) {
            break;
        }
    }
    uint32_t end = to % NGREP_RINGBUFFER_SIZE;
    while (end != ns->end % NGREP_RINGBUFFER_SIZE) {
        if (ns->buffer[end] == '\n' || ns->buffer[end] == '\r') {
            break;
        }
        end = (end + 1) % NGREP_RINGBUFFER_SIZE;
    }
    for (uint32_t i = start; i != end; i = (i+1) % NGREP_RINGBUFFER_SIZE) {
        if (ns->buffer[i] == '%') {
            printf("%%%02x", ns->buffer[i]);
        } else if (isprint(ns->buffer[i])) {
            printf("%c", ns->buffer[i]);
        } else {
            printf("%%%02x", ns->buffer[i]);
        }
        
    }
    printf("\n");
    return end;
}

static int MatchTcpEvent(unsigned int id, unsigned long long from,
                         unsigned long long to, unsigned int flags, void *context)
{
    NgrepStorageStream * ctx = (NgrepStorageStream*) context;
    if (ctx->last > to) {
        return 0;
    }
    ctx->last = NgrepRingPrint(ctx, to);
    return 0;
}

static void NgrepFillRingBuffer(NgrepStorageStream *ns, uint8_t *data, uint32_t data_len) {
    ns->data = data;
    ns->data_len = data_len;
    for (uint32_t i = 0; i < data_len; i++) {
        ns->buffer[(ns->end + i) % NGREP_RINGBUFFER_SIZE] = data[i];
    }
    ns->end += data_len;
}

static bool NgrepTCPCallback(uint8_t *data, uint32_t data_len, uint8_t flags, Flow *f) {
    NgrepStorageStreams *nss = (NgrepStorageStreams *)FlowGetStorageById(f, g_flow_storage_ngrep_id);
    if (nss == NULL) {
        nss = malloc(sizeof(NgrepStorageStreams));
        memset(nss, 0, sizeof(NgrepStorageStreams));
        if (hs_open_stream(hs_db_stream, 0, &nss->toc.hstr) != HS_SUCCESS) {
            fprintf(stderr, "hs_open_stream failed\n");
            return true;
        }
        if (hs_open_stream(hs_db_stream, 0, &nss->tos.hstr) != HS_SUCCESS) {
            fprintf(stderr, "hs_open_stream failed\n");
            return true;
        }
        FlowSetStorageById(f, g_flow_storage_ngrep_id, nss);
    }

    NgrepStorageStream *ns;
    if (flags & STREAM_TOCLIENT) {
        ns = &nss->toc;
    } else if (flags & STREAM_TOSERVER) {
        ns = &nss->tos;
    } else {
        fprintf(stderr, "flags is neither STREAM_TOCLIENT nor STREAM_TOSERVER\n");
        return true;
    }
    if (data == NULL && data_len == 0) {
        // eof
        hs_close_stream(ns->hstr, scratch_stream, MatchTcpEvent, NULL);
        FlowSetStorageById(f, g_flow_storage_ngrep_id, NULL);
    } else if (data == NULL) {
        // gap
        if (hs_reset_stream(ns->hstr, 0, scratch_stream, MatchTcpEvent, NULL) != HS_SUCCESS) {
            fprintf(stderr, "warning, hs_reset_stream failed\n");
        }
        ns->end = 0;
    } else {
        // ctx structure with a ring buffer of some sort
        // because previous data got forgotten by suricata
        NgrepFillRingBuffer(ns, data, data_len);
        if (hs_scan_stream(ns->hstr, (const char *) data, data_len, 0, scratch_stream, MatchTcpEvent, ns) != HS_SUCCESS) {
            fprintf(stderr, "warning, hs_scan failed\n");
        }
    }
    // stop further app-layer processing by suricata
    return true;
}

static void libsuricata_init() {
    // init libsuricata
    // TODOlib just one helper function for all
    InitGlobal();

    GlobalsInitPreConfig();
    run_mode = RUNMODE_PCAP_FILE;

    PostConfLoadedSetup(&surifuzz);
    PreRunPostPrivsDropInit(run_mode);
    PostConfLoadedDetectSetup(&surifuzz);

    memset(&tv, 0, sizeof(tv));
    tv.flow_queue = FlowQueueNew();
    if (tv.flow_queue == NULL)
        abort();
    dtv = DecodeThreadVarsAlloc(&tv);
    DecodeRegisterPerfCounters(dtv, &tv);
    tmm_modules[TMM_FLOWWORKER].ThreadInit(&tv, NULL, &fwd);
    StatsSetupPrivate(&tv);

    extern intmax_t max_pending_packets;
    max_pending_packets = 128;
    PacketPoolInit();
    AppLayerTCPDataCallback = NgrepTCPCallback;
}

static void NgrepFlowStorageFree(void *nhs) {
    NgrepStorageStreams *nss = (NgrepStorageStreams*) nhs;
    hs_close_stream(nss->toc.hstr, scratch_stream, MatchTcpEvent, NULL);
    hs_close_stream(nss->tos.hstr, scratch_stream, MatchTcpEvent, NULL);
}

typedef struct NgrepMatchContext {
    Packet *p;
    uint32_t last;
} NgrepMatchContext;


static int MatchUdpEvent(unsigned int id, unsigned long long from,
                      unsigned long long to, unsigned int flags, void *context)
{
    NgrepMatchContext *ctx = (NgrepMatchContext *) context;
    if (ctx->last > to) {
        return 0;
    }
    Packet *p = ctx->p;
    // we could print information about the Flow
    ctx->last = NgrepPrint(p->payload, p->payload_len, from, to);
    return 0;
}

int main(int argc, char** argv)
{
    Packet *p;
    int r = 0;

    // TODOlib : use libsuricata to parse cmdline
    // and get the right source for packets
    if (argc != 3) {
        printf("Please provide exactly two argument : a pattern and a pcap file\n");
        return 1;
    }

    hs_database_t *hs_db_block = NULL;
    hs_compile_error_t *compile_err = NULL;
    //TODOask use HS_FLAG_SOM_LEFTMOST ?
    if (hs_compile(argv[1], 0, HS_MODE_BLOCK, NULL, &hs_db_block,
                   &compile_err) != HS_SUCCESS) {
        fprintf(stderr, "hs_compile failed for %s\n", argv[1]);
        hs_free_compile_error(compile_err);
        r = 2;
        goto end;
    }
    if (hs_compile(argv[1], 0, HS_MODE_STREAM, NULL, &hs_db_stream,
                   &compile_err) != HS_SUCCESS) {
        fprintf(stderr, "hs_compile failed for %s\n", argv[1]);
        hs_free_compile_error(compile_err);
        r = 2;
        goto end;
    }
    hs_scratch_t *scratch_block;
    if (hs_alloc_scratch(hs_db_block, &scratch_block)) {
        fprintf(stderr, "hs_alloc_scratch failed\n");
        r = 2;
        goto end;
    }
    if (hs_alloc_scratch(hs_db_stream, &scratch_stream)) {
        fprintf(stderr, "hs_alloc_scratch failed\n");
        r = 2;
        goto end;
    }

    NgrepMatchContext hs_ctx_udp;
    g_flow_storage_ngrep_id = FlowStorageRegister("ngrep", sizeof(void *), NULL, NgrepFlowStorageFree);

    setenv("SC_LOG_OP_IFACE", "file", 0);
    setenv("SC_LOG_FILE", "/dev/null", 0);
    libsuricata_init();

    // libpcap : initialize structure
    pcap_t * pkts;
    char errbuf[PCAP_ERRBUF_SIZE];
    const u_char *pkt;
    struct pcap_pkthdr *header;

    pkts = pcap_open_offline(argv[2], errbuf);
    if (pkts == NULL) {
        fprintf(stderr, "pcap_open_offline failed with %s\n", errbuf);
        r = 2;
        goto end;
    }

    p = PacketGetFromAlloc();
    while (pcap_next_ex(pkts, &header, &pkt) > 0) {
        // translate a libpcap packet into a suricata packet
        p->ts.tv_sec = header->ts.tv_sec;
        p->ts.tv_usec = header->ts.tv_usec;
        p->datalink = pcap_datalink(pkts);
        if (PacketSetData(p, pkt, header->caplen) != 0) {
            fprintf(stderr, "PacketSetData failed\n");
            r = 2;
            goto end;
        }

        TmEcode ecode = tmm_modules[TMM_DECODEPCAPFILE].Func(&tv, p, dtv);
        if (ecode == TM_ECODE_FAILED) {
            break;
        }
        Packet *extra_p = PacketDequeueNoLock(&tv.decode_pq);
        while (extra_p != NULL) {
            // TODOask should we process these extra packets ?
            // with decoding ? or only worker ?
            // What are these pseudo packets ? Tunnel decapsulation ?
            PacketFreeOrRelease(extra_p);
            extra_p = PacketDequeueNoLock(&tv.decode_pq);
        }

        if (p->proto == IPPROTO_UDP) {
            hs_ctx_udp.p = p;
            hs_ctx_udp.last = 0;
            if (hs_scan(hs_db_block, (const char *) p->payload, p->payload_len, 0, scratch_block, MatchUdpEvent, &hs_ctx_udp) != HS_SUCCESS) {
                fprintf(stderr, "warning, hs_scan failed\n");
            }
        } else {
            tmm_modules[TMM_FLOWWORKER].Func(&tv, p, fwd);
            extra_p = PacketDequeueNoLock(&tv.decode_pq);
            while (extra_p != NULL) {
                PacketFreeOrRelease(extra_p);
                extra_p = PacketDequeueNoLock(&tv.decode_pq);
            }
        }

        PACKET_RECYCLE(p);
    }
    //TODOask timeout/terminate all the flows

end:
    // closing and releasing
    pcap_close(pkts);
    PacketFree(p);
    hs_free_scratch(scratch_block);
    hs_free_database(hs_db_block);
    hs_free_database(hs_db_stream);

    return r;
}

