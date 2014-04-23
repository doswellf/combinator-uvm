
#-------------------------------------------------------------------------
# File name   : Makefile
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


## Variables and scripts
NCROOT            = `ncroot`
TEST_NAME         = apb_subsystem_test 
SVSEED            = random
NCLIBDIRPATH      = .
TB_FILENAME       = ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/sv/apb_subsystem_top.sv
VERBOSITY         = HIGH
WORKSHOP_MODE     = NONE
## CMS_TOP_FILES     = ""


OPTIONS    = -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/ahb/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/apb/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/uart/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/spi/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/gpio/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/sequence_lib \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/sv  \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/sv/sequence_lib  \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/sv  \
             -incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/tests \
             ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/uart16550/rtl/uart_defines.v \
             ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/opencores/spi/rtl/spi_defines.v \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/sv/gpio_defines.svh \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/sv/spi_defines.svh \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_defines.svh \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/sv/apb_subsystem_defines.svh \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/ahb/sv/ahb_pkg.sv \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/apb/sv/apb_pkg.sv \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/uart/sv/uart_pkg.sv \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/gpio/sv/gpio_pkg.sv \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/spi/sv/spi_pkg.sv \
             -F ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/apb_subsystem/rtl/apb_subsystem.irunargs \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_pkg.sv \
             ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/sv/apb_subsystem_pkg.sv \
             +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/assert_opt.tcl \
             -assert_count_traces \
             -nowarn ZROMCV \
             -nowarn COVDCL \
             +UVM_VERBOSITY=$(VERBOSITY) \
             +UVM_TESTNAME=$(TEST_NAME) \
             +define+LITLE_ENDIAN \
             +svseed+${SVSEED} \
             -nclibdirpath $(NCLIBDIRPATH) \
             -TIMESCALE 1ns/10ps \
             -access +rwc \
             $(TB_FILENAME) 


ASRT_OPTION = +define+UART_ABV_ON

GUI_OPTIONS = $(OPTIONS) $(ASRT_OPTION) \
              -gui \
              +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/nc_waves.tcl

#added options for waveforms for batch debug simulations (no gui)
WAVE_OPTIONS = $(OPTIONS) $(ASRT_OPTION) \
              +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/nc_waves.tcl

COV_OPTIONS = -covfile ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/covfile.cf \
              -coverage functional \
              -covoverwrite \
              -covtest $(TEST_NAME) \
              -covdut apb_subsystem_top

BATCH_OPTIONS = +tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/run_batch.tcl

CMS_OPTIONS = -define "CMS_TEST" \
              -snprerun "load $(CMS_TOP_FILES)"

IRUN = irun -sv -uvmhome ${UVM_HOME}

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

test_cms : run_cms

# use with run_mode=interactive and run_mode=interactive_debug
run_gui : 
	${IRUN} $(GUI_OPTIONS) $(COV_OPTIONS)

# added target for batch debug with waves
# use with run_mode=batch_debug
run_wave : 
	${IRUN} $(WAVE_OPTIONS) $(COV_OPTIONS) $(BATCH_OPTIONS)

# use with run_mode=batch
run_nogui : 
	${IRUN} $(OPTIONS) $(ASRT_OPTION) $(COV_OPTIONS) $(BATCH_OPTIONS)

run_cms : 
	${IRUN} $(OPTIONS) $(COV_OPTIONS) $(BATCH_OPTIONS) $(CMS_OPTIONS)

run_nocov : 
	${IRUN} $(OPTIONS) $(ASRT_OPTION) $(BATCH_OPTIONS)





