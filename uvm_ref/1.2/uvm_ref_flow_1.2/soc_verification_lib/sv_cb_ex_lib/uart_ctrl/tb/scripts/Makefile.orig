
#-------------------------------------------------------------------------
# File name   : Makefile
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


## Variables and scripts
NCROOT            = `ncroot`
TEST_NAME         = apb_uart_rx_tx 
SVSEED            = random
NCLIBDIRPATH      = .
TB_FILENAME       = ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/sv/uart_ctrl_top.sv
VERBOSITY         = MEDIUM
WORKSHOP_MODE     = NONE


OPTIONS    = -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/apb/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/uart/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv  \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/sequence_lib  \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/sv  \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/tests  \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/apb/sv/apb_pkg.sv \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/uart/sv/uart_pkg.sv \
             ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/uart16550/rtl/uart_defines.v \
             -F ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/oc_uart.irunargs \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_defines.svh \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_pkg.sv \
             -assert_count_traces \
             -nowarn COVSEC \
             +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/scripts/assert_opt.tcl \
             +svseed+${SVSEED} \
             -nclibdirpath $(NCLIBDIRPATH) \
             +UVM_VERBOSITY=$(VERBOSITY) \
             +UVM_TESTNAME=$(TEST_NAME) \
             +define+UART_ABV_ON \
             +define+LITLE_ENDIAN \
             -assert_logging_error_off \
             +define+DYNAMIC_SIM \
             -propfile_vlog ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/uart16550/assertions/receiver_vunit.psl \
             -propfile_vlog ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/uart16550/assertions/rx_fifo_vunit.psl \
             -propfile_vlog ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/uart16550/assertions/transmitter_vunit.psl \
             -propfile_vlog ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/uart16550/assertions/tx_fifo_vunit.psl \
             $(TB_FILENAME) 

GUI_OPTIONS = $(OPTIONS) \
              -gui \
              -access +rwc \
              +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/scripts/nc_waves.tcl

#added options for waveforms for batch debug simulations (no gui)
WAVE_OPTIONS = $(OPTIONS) \
              +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/scripts/nc_waves.tcl

COV_OPTIONS = -covfile ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/scripts/covfile.cf \
              -coverage functional \
              -covoverwrite \
              -covtest $(TEST_NAME) \
              -covdut uart_ctrl_top

BATCH_OPTIONS = +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/tb/scripts/run_batch.tcl

IRUN = irun -uvmhome ${UVM_HOME} -assert -sv -define $(WORKSHOP_MODE)

#******************************************************************************#
# Targets
#******************************************************************************#

# use with run_mode=batch
test       : run_nogui

# use with run_mode=interactive and run_mode=interactive_debug
test_gui : run_gui 

# added target for batch debug with waves
# use with run_mode=batch_debug
test_wave : run_wave 

test_nocov : run_nocov

# use with run_mode=interactive and run_mode=interactive_debug
run_gui : 
	${IRUN} $(GUI_OPTIONS) $(COV_OPTIONS)

# added target for batch debug with waves
# use with run_mode=batch_debug
run_wave : 
	${IRUN} $(WAVE_OPTIONS) $(COV_OPTIONS) $(BATCH_OPTIONS)

# use with run_mode=batch
run_nogui : 
	${IRUN} $(OPTIONS) $(COV_OPTIONS) $(BATCH_OPTIONS)

run_nocov : 
	${IRUN} $(OPTIONS) $(BATCH_OPTIONS)

clean:
	rm -rf INCA* *.log *.key .simvis* waves* *.shm  *~ cov_work

