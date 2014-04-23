// IVB checksum: 720351203
/*-----------------------------------------------------------------
File name     : ahb_pkg.sv
Created       : Wed May 19 15:42:21 2010
Description   : This file imports all the files of the OVC.
Notes         :
-----------------------------------------------------------------*/
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


`ifndef AHB_PKG_SV
`define AHB_PKG_SV

package ahb_pkg;

// UVM class library compiled in a package
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "ahb_defines.sv"
`include "ahb_transfer.sv"

`include "ahb_master_monitor.sv"
`include "ahb_master_sequencer.sv"
`include "ahb_master_driver.sv"
`include "ahb_master_collector.sv"
`include "ahb_master_agent.sv"
// Can include universally reusable master sequences here.

`include "ahb_slave_monitor.sv"
`include "ahb_slave_sequencer.sv"
`include "ahb_slave_driver.sv"
`include "ahb_slave_collector.sv"
`include "ahb_slave_agent.sv"
// Can include universally reusable slave sequences here.

`include "ahb_env.sv"
`include "reg_to_ahb_adapter.sv"

endpackage : ahb_pkg

`endif // AHB_PKG_SV
