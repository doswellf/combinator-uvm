#! /bin/bash
# set -xv

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

if [ -z "${UNILANG_OVERRIDE+x}" ] ; then
  echo "Error: Environment variable UNILANG_OVERRIDE should point to the directory where libml_uvm.so is located. The directory path must have a terminal '/' character"
  exit
fi

irun -64bit -nocopyright -debug +incdir+. +UVM_NO_RELNOTES -uvmtop SC:sctop -uvmtop SV:test -sysc sctop.cpp test.sv -top topmodule  -sv_lib ${UNILANG_OVERRIDE}/libml_uvm.so
