#!/bin/sh -f

#-------------------------------------------------------------------------
# File name   : vm_run.sh
# Title       :
# Project     : UART Block Level Verification
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

if [ ! -n "$UVM_HOME" ]; then
UVM_HOME=`ncroot`/tools/uvm-1.1
export UVM_HOME
fi

# Create common build area for each test case
snapshot_path=${BRUN_SESSION_DIR}/session_build
if [ -d $snapshot_path ]; then
   echo "Using NCLIBDIRPATH = $snapshot_path"
else
   echo "Creating NCLIBDIRPATH = $snapshot_path"
   mkdir -p $snapshot_path
fi


# Options based on re-run mode
case "$BRUN_RUN_MODE" in
    interactive)
        make_target="test_gui"
        make_options="VERBOSITY=MEDIUM"
        ;;
    interactive_debug)
        make_target="test_gui"
        make_options="VERBOSITY=HIGH"
        ;;
    batch_debug)
        make_target="test_wave"
        make_options="VERBOSITY=HIGH"
        ;;
    # default to batch
    *)
        make_target="test"
        make_options="VERBOSITY=LOW"
        ;;
esac


# detect WORKSHOP_MODE
if [ $# != 0 ]; then 
  if [ "$1" = "UVM_WKSHP" ]; then 
    make_options="$make_options WORKSHOP_MODE=UVM_WKSHP"
  fi
fi

# invoke Makefile with appropriate options
echo "make_target=$make_target"
echo "make_options=$make_options"
gmake -f ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/scripts/Makefile $make_options NCLIBDIRPATH=${snapshot_path} TEST_NAME=${BRUN_TEST_NAME} SVSEED=${BRUN_SV_SEED} $make_target


