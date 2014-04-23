#!/bin/csh -f
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
if (! $?UVM_ML_HOME) then
setenv UVM_ML_HOME $PWD
endif

if ( ! $?UVM_ML_CC) then
setenv UVM_ML_CC `which g++`
endif

if ( ! $?UVM_ML_LD) then
setenv UVM_ML_LD $UVM_ML_CC
endif

if ( ! $?UVM_ML_SVDPI_DIR ) then
setenv UVM_ML_SVDPI_DIR $MTI_HOME/include
endif

# This release uses a specific ML ready version of UVM-SV 1.1c, so to avoid using 
# an incompatible version:
if ( ! $?UVM_HOME) then
    setenv UVM_HOME $UVM_ML_HOME/ml/frameworks/uvm/sv/uvm-1.1c
endif

source $UVM_ML_HOME/ml/setup.sh --no-ncsc $*
