# UVM_ML setup capture
# Performed at Wed Nov 13 14:59:02 IST 2013

if ( !  $?UVM_ML_HOME  ) then 
setenv  UVM_ML_HOME '/home/alexch/babelfish/20131113/babeldag' 
endif

if ( !  $?OSCI_INSTALL  ) then 
setenv  OSCI_INSTALL '/cad/tools/osci/2.2/g++-4.4.5-pic' 
endif

if ( !  $?OSCI_SRC  ) then 
setenv  OSCI_SRC '/dv/tools/3rdParty/systemc/systemc-2.2.0' 
endif

if ( !  $?TLM2_INSTALL  ) then 
setenv  TLM2_INSTALL '/home/gabi/TLM-2009-07-15/' 
endif

if ( !  $?UVM_ML_CC  ) then 
setenv  UVM_ML_CC '/cad/tools/cadence/IUS13.1_latest/linux/tools/cdsgcc/gcc/4.4/bin/g++' 
endif

if ( !  $?UVM_ML_LD  ) then 
setenv  UVM_ML_LD '/cad/tools/cadence/IUS13.1_latest/linux/tools/cdsgcc/gcc/4.4/bin/g++' 
endif

if ( !  $?UVM_ML_SVDPI_DIR  ) then 
setenv  UVM_ML_SVDPI_DIR '/cad/tools/cadence/IUS13.1_latest/linux/tools/include' 
endif

if ( !  $?UVM_ML_COMPILER_VERSION  ) then 
setenv  UVM_ML_COMPILER_VERSION '4.4' 
endif

if ( !  $?UVM_ML_OVERRIDE  ) then 
setenv  UVM_ML_OVERRIDE '/home/alexch/babelfish/20131113/babeldag/ml/libs/backplane/4.4/64bit/' 
endif

if ( !  $?UNILANG_OVERRIDE  ) then 
setenv  UNILANG_OVERRIDE '/home/alexch/babelfish/20131113/babeldag/ml/libs/backplane/4.4/64bit/' 
endif

if ( !  $?IES_VERSION  ) then 
setenv  IES_VERSION '13.1' 
endif

if ( !  $?OSCI_VERSION  ) then 
setenv  OSCI_VERSION '2.2' 
endif

