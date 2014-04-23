#! /bin/bash
#
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
# clean_in_between=""
# to_stop=0
run_64bit=0
run_32bit=0
run_osci=1
run_ncsc=1
tests_to_run=""
# run_specman=0


for parameter in $*
do 
    if [ "$parameter" == "--64bit" ]; then
        run_64bit=1
    elif [ "$parameter" == "--32bit" ]; then
        run_32bit=1
    elif [ "$parameter" == "--no-osci" ]; then
        run_osci=0
    elif [ "$parameter" == "--no-ncsc" ]; then
        run_ncsc=0
    fi
done

if [ $run_64bit -eq 0 -a $run_32bit -eq 0 ]; then
    run_64bit=1
fi



if [ $run_osci -eq 1 ]; then
    tests_to_run="$tests_to_run ies_osci_cl ies_osci_proc ies_osci_cl_multistep ies_osci_proc_multistep"
fi

if [ $run_ncsc -eq 1 ]; then
    tests_to_run="$tests_to_run ies_ncsc_cl ies_ncsc_proc ies_ncsc_cl_multistep ies_ncsc_proc_multistep"
fi

if [ "$tests_to_run" == "" ]; then
    tests_to_run="ies"
fi



./test_runner.sh $* $tests_to_run


