
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


-incdir ${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib/ahb/sv \
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
+tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/lp_control.tcl \
-assert_count_traces \
${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/sv/apb_subsystem_top.sv \
+tcl+${SOCV_KIT_HOME}/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/tb/scripts/nc_waves_lp.tcl \
+UVM_VERBOSITY=MEDIUM \
+define+LITLE_ENDIAN \
+svseed+1 \
-nclibdirpath . \
-TIMESCALE 1ns/10ps \
-access +rwc \
+define+UART_ABV_ON 



