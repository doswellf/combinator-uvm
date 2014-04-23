/*-------------------------------------------------------------------------
File name   : uart_pkg.svh
Title       : Package for UART UVC
Project     :
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

  
`ifndef UART_PKG_SV
`define UART_PKG_SV

package uart_pkg;

// Import the UVM library and include the UVM macros
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "uart_config.sv" 
`include "uart_frame.sv"
`include "uart_monitor.sv"
`include "uart_rx_monitor.sv"
`include "uart_tx_monitor.sv"
`include "uart_sequencer.sv"
`include "uart_tx_driver.sv"
`include "uart_rx_driver.sv"
`include "uart_tx_agent.sv"
`include "uart_rx_agent.sv"
`include "uart_env.sv"
`include "uart_seq_lib.sv"

endpackage : uart_pkg
`endif  // UART_PKG_SV
