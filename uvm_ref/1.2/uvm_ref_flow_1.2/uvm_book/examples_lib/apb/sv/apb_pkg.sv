/*-------------------------------------------------------------------------
File name   : apb_pkg.sv
Title       : Package for APB UVC
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

package apb_pkg;

// Import the UVM class library  and UVM automation macros
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "sv/apb_config.sv"
`include "sv/apb_types.sv"
`include "sv/apb_transfer.sv"
`include "sv/apb_monitor.sv"
`include "sv/apb_collector.sv"

`include "sv/apb_master_driver.sv"
`include "sv/apb_master_sequencer.sv"
`include "sv/apb_master_agent.sv"

`include "sv/apb_slave_driver.sv"
`include "sv/apb_slave_sequencer.sv"
`include "sv/apb_slave_agent.sv"

`include "sv/apb_master_seq_lib.sv"
`include "sv/apb_slave_seq_lib.sv"

`include "sv/apb_env.sv"

`include "sv/reg_to_apb_adapter.sv"

endpackage : apb_pkg
