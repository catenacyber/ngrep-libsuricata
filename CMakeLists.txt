cmake_minimum_required (VERSION 3.0)

project (ngrep C)
set(NGREP_MAJOR_VERSION 0)
set(NGREP_MINOR_VERSION 1)
set(NGREP_MICRO_VERSION 0)
set(NGREP_VERSION ${NGREP_MAJOR_VERSION}.${NGREP_MINOR_VERSION}.${NGREP_MICRO_VERSION})

find_library(PCAP_LIB pcap)
find_library(HS_LIB hs)

# TODOlibs mine does not set `CFLAGS=-DOS_DARWIN=1` even if it is needed
execute_process(COMMAND libsuricata-config --cflags OUTPUT_VARIABLE LIBSURI_CFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND libsuricata-config --libs OUTPUT_VARIABLE LIBSURI_LIBS1 OUTPUT_STRIP_TRAILING_WHITESPACE)
string(STRIP ${LIBSURI_LIBS1} LIBSURI_LIBS)
separate_arguments(LIBSURI_LIBS)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${LIBSURI_CFLAGS}")

set(ngrep_src main.c)

add_executable (ngrep_bin ${ngrep_src})
target_link_libraries (ngrep_bin ${PCAP_LIB} ${HS_LIB} ${LIBSURI_LIBS})

install(TARGETS ngrep_bin)
