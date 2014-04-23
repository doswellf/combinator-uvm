# UVM_ML setup capture
# Performed at Wed Nov 13 14:59:02 IST 2013

ifndef UVM_ML_HOME
UVM_ML_HOME :=  /home/alexch/babelfish/20131113/babeldag
export UVM_ML_HOME
endif

ifndef OSCI_INSTALL
OSCI_INSTALL :=  /cad/tools/osci/2.2/g++-4.4.5-pic
export OSCI_INSTALL
endif

ifndef OSCI_SRC
OSCI_SRC :=  /dv/tools/3rdParty/systemc/systemc-2.2.0
export OSCI_SRC
endif

ifndef TLM2_INSTALL
TLM2_INSTALL :=  /home/gabi/TLM-2009-07-15/
export TLM2_INSTALL
endif

ifndef UVM_ML_CC
UVM_ML_CC :=  /cad/tools/cadence/IUS13.1_latest/linux/tools/cdsgcc/gcc/4.4/bin/g++
export UVM_ML_CC
endif

ifndef UVM_ML_LD
UVM_ML_LD :=  /cad/tools/cadence/IUS13.1_latest/linux/tools/cdsgcc/gcc/4.4/bin/g++
export UVM_ML_LD
endif

ifndef UVM_ML_SVDPI_DIR
UVM_ML_SVDPI_DIR :=  /cad/tools/cadence/IUS13.1_latest/linux/tools/include
export UVM_ML_SVDPI_DIR
endif

ifndef UVM_ML_COMPILER_VERSION
UVM_ML_COMPILER_VERSION :=  4.4
export UVM_ML_COMPILER_VERSION
endif

ifndef UVM_ML_OVERRIDE
UVM_ML_OVERRIDE :=  /home/alexch/babelfish/20131113/babeldag/ml/libs/backplane/4.4/64bit/
export UVM_ML_OVERRIDE
endif

ifndef UNILANG_OVERRIDE
UNILANG_OVERRIDE :=  /home/alexch/babelfish/20131113/babeldag/ml/libs/backplane/4.4/64bit/
export UNILANG_OVERRIDE
endif

ifndef IES_VERSION
IES_VERSION :=  13.1
export IES_VERSION
endif

ifndef OSCI_VERSION
OSCI_VERSION :=  2.2
export OSCI_VERSION
endif

