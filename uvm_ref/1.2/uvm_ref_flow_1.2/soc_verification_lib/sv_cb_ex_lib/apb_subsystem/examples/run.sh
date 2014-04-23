#!/bin/sh -f

#-------------------------------------------------------------------------
# File name   : run.sh
# Title       :
# Project     : APB Subsystem Level Verification
# Created     :
# Description :
# Notes       :
#----------------------------------------------------------------------
#   Copyright 1999-2010 Cadence Design Systems, Inc.
#   All Rights Reserved Worldwide
#
#   Licensed under the Apache License, Version 2.0 (the
#   "License"); you may not use this file except in
#   compliance with the License.  You may obtain a copy of
#   the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in
#   writing, software distributed under the License is
#   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
#   CONDITIONS OF ANY KIND, either express or implied.  See
#   the License for the specific language governing
#   permissions and limitations under the License.
#----------------------------------------------------------------------

if [ ! -n "$SOCV_KIT_HOME" ]; then
   echo "SOCV_KIT_HOME is not set."
   echo "Please set it to your installation "
   exit
fi

if [ ! -n "$UVM_HOME" ]; then
UVM_HOME=`ncroot`/tools/uvm-1.1
export UVM_HOME
fi
usage() {
    echo "Usage:  demo.sh [-test <test_name>]"
    echo "                [-seed <value>]"
    echo "                [-v[erbosity] <verbosity>]"
    echo "                [-r[un_mode]  { test | test_gui }]"
    echo ""
    echo "        demo.sh -h[elp]"
    echo ""
    echo "Where:"
    echo "  <verbosity> is one of: { NONE | LOW | MEDIUM | HIGH | FULL }"
    echo "  <test_name> is one of the classes defined in: `/bin/ls $SOCV_KIT_HOME/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/tests` "
   
}

# =============================================================================
# Get args
# =============================================================================
test="";
gui=""
seed="";
run_mode="test";
severity="";
verbosity="";
cov_enabled=1;
cov_commands="";
while [ $# -gt 0 ]; do
   case `echo $1 | tr "[A-Z]" "[a-z]"` in
      -h|-help)
                        usage
                        exit 1
                        ;;
      -test)
                        test=" TEST_NAME=$2"
                        shift
                        ;;
      -seed)
                        seed=" SVSEED=$2"
                        shift
                        ;;
      -r|-run_mode)
                        run_mode=$2
                        shift
                        ;;
      -v|-verbosity)
                        verbosity=" VERBOSITY=$2"
                        shift
                        ;;
     
       esac
    shift       
done


gmake -f ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/Makefile $seed $run_mode $verbosity $test

