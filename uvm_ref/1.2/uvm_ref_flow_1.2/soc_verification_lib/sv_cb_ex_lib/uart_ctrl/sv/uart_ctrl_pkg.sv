/*-------------------------------------------------------------------------
File name   : uart_ctrl_pkg.svh
Title       : Module UVC Files
Project     : UART Block Level
Created     :
Description : 
Notes       : 
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------


`ifndef UART_CRTL_PKG_SV
`define UART_CRTL_PKG_SV

package uart_ctrl_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

import apb_pkg::*;
import uart_pkg::*;

`include "uart_ctrl_config.sv"
`include "uart_ctrl_reg_model.sv"
//`include "reg_to_apb_adapter.sv"
`include "uart_ctrl_scoreboard.sv"
`include "coverage/uart_ctrl_cover.sv"
`include "uart_ctrl_monitor.sv"
//`include "uart_ctrl_reg_sequencer.sv"    //KAM - Remove
`include "uart_ctrl_virtual_sequencer.sv"
`include "uart_ctrl_env.sv"

endpackage : uart_ctrl_pkg

`endif //UART_CTRL_PKG_SV
