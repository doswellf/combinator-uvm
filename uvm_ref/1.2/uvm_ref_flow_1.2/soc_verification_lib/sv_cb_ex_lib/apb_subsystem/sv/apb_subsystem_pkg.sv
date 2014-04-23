/*-------------------------------------------------------------------------
File name   : apb_subsystem_pkg.sv
Title       : Module UVC Files
Project     : APB Subsystem Level
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


`ifndef APB_SUBSYSTEM_PKG_SV
`define APB_SUBSYSTEM_PKG_SV

package apb_subsystem_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

import ahb_pkg::*;
import apb_pkg::*;
import uart_pkg::*;
import spi_pkg::*;
import gpio_pkg::*;
import uart_ctrl_pkg::*;

`include "apb_subsystem_config.sv"
//`include "reg_to_ahb_adapter.sv"
`include "apb_subsystem_scoreboard.sv"
`include "apb_subsystem_monitor.sv"
`include "apb_subsystem_env.sv"

endpackage : apb_subsystem_pkg

`endif //APB_SUBSYSTEM_PKG_SV
