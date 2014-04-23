/*-------------------------------------------------------------------------
File name   : gpio_pkg.svh
Title       : Package for GPIO OVC
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

  
`ifndef GPIO_PKG_SVH
`define GPIO_PKG_SVH

package gpio_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

//////////////////////////////////////////////////
//        UVM Class Forward Declarations        //
//////////////////////////////////////////////////

typedef class gpio_agent;
typedef class gpio_csr;
typedef class gpio_driver;
typedef class gpio_env;
typedef class gpio_monitor;
typedef class gpio_simple_trans_seq;
typedef class gpio_multiple_simple_trans;
typedef class gpio_sequencer;
typedef class gpio_transfer;

//////////////////////////////////////////////////
//              Include files                   //
//////////////////////////////////////////////////
`include "gpio_csr.sv"
`include "gpio_transfer.sv"
`include "gpio_config.sv"

`include "gpio_monitor.sv"
`include "gpio_sequencer.sv"
`include "gpio_driver.sv"
`include "gpio_agent.sv"

`include "gpio_env.sv"

`include "gpio_seq_lib.sv"

endpackage : gpio_pkg

`endif
