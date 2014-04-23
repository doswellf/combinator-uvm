#! /bin/tcsh -f
##
################################################
##
## test_install.sh
##         This file helps to test the installation was done 
##         correctly. It prints out tool version info and echoes
##         the environment variables used by UVM-ML, for the 
##         user to examine and verify.
##         
## -------------------------------------------------------------
##    Copyright 2012 Cadence.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
## 
################################################

echo "########## BEGIN_TESTING ##########"


which g++
echo "g++ version:"
g++ --version
which specman
which vcs
which vsim

echo "ncroot " `ncroot`

if ( $?IES_VERSION ) then
echo "IES_VERSION " $IES_VERSION 
else
echo "IES_VERSION is undefined"
endif 

if ( $?IES_VERSION ) then
echo "OSCI_VERSION " $OSCI_VERSION
else
echo "OSCI_VERSION is undefined" 
endif

if ( $?UVM_ML_HOME ) then
echo "UVM_ML_HOME " $UVM_ML_HOME
echo "UVM_ML_HOME/ml:"
ls $UVM_ML_HOME/ml
echo "timestamp:"
cat $UVM_ML_HOME/ml/timestamp.txt
else
echo "UVM_ML_HOME is undefined"
endif

if ( $?TLM2_INSTALL ) then
echo "TLM2_INSTALL " $TLM2_INSTALL
echo "TLM2_INTSTALL:"
ls $TLM2_INSTALL
else 
echo "TLM2_INSTALL is undefined" 
endif

if ( $?OSCI_SRC ) then
echo "OSCI_SRC " $OSCI_SRC
echo "OSCI_SRC:"
ls $OSCI_SRC
else
echo "OSCI_SRC is undefined"
endif

if ( $?OSCI_INSTALL ) then 
echo "OSCI_INSTALL " $OSCI_INSTALL
echo "OSCI_INSTALL:"
ls $OSCI_INSTALL
else
echo "OSCI_INSTALL is undefined"
endif

if ( $?UVM_ML_CC ) then
echo "UVM_ML_CC " $UVM_ML_CC
echo "CDNS g++ version:"
$UVM_ML_CC --version
else
echo "UVM_ML_CC is undefined"
endif

if ( $?UVM_ML_SVDPI_DIR ) then
echo "UVM_ML_SVDPI_DIR " $UVM_ML_SVDPI_DIR
else
echo "UVM_ML_HOME is undefined"
endif

if ( ($?UVM_HOME) ) then
  echo "UVM_HOME " $UVM_HOME
else
echo "UVM_HOME is undefined"
endif


if ($?UNILANG_OVERRIDE) then
echo "UNILANG_OVERRIDE " $UNILANG_OVERRIDE
if (! -d ${UNILANG_OVERRIDE} ) then 
    echo "FIXME: UNILANG_OVERRIDE should point to a directory. Trailing slash is mandatory!"
else if ( ! -f ${UNILANG_OVERRIDE}libml_uvm.so  ) then
    echo "FIXME: Wrong value or missing trailing slash in UNILANG_OVERRIDE"
endif
    
endif
else 
echo "UNILANG_OVERRIDE is undefined"
endif

if ($?UVM_ML_OVERRIDE) then
echo "UVM_ML_OVERRIDE:" $UVM_ML_OVERRIDE
else
echo "UVM_ML_OVERRIDE is undefined"
endif

echo "####### END TESTING ##########" 
