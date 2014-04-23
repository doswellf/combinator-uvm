#!/bin/bash -e
${UVM_ML_CC} -I${OSCI_INSTALL}/include ${UVM_ML_HOME}/ml/tools/osci_version.cpp -o /tmp/osci_version.exe -Wl,--whole-archive ${OSCI_INSTALL}/lib-linux64/libsystemc.a -Wl,--no-whole-archive -lpthread
/tmp/osci_version.exe 2>&1 | tail -n 1
rm -f /tmp/osci_version.exe
