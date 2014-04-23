/*-------------------------------------------------------------------------
File name   : gpio_transfer.sv
Title       : GPIO SystemVerilog UVM OVC
Project     : SystemVerilog UVM Cluster Level Verification
Created     :
Description : 
Notes       :  
---------------------------------------------------------------------------*/
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


`ifndef GPIO_TRANSFER_SV
`define GPIO_TRANSFER_SV

class gpio_transfer extends uvm_sequence_item;

  rand int unsigned delay;

  rand bit [`GPIO_DATA_WIDTH-1:0] transfer_data;
  bit [`GPIO_DATA_WIDTH-1:0] monitor_data;
  bit [`GPIO_DATA_WIDTH-1:0] output_enable;

  string agent = "";        //updated my monitor - scoreboard can use this

  constraint c_default_delay {delay >= 0; delay < 20;}

  // These declarations implement the create() and get_type_name() as well as enable automation of the
  // transfer fields   
  `uvm_object_utils_begin(gpio_transfer)
    `uvm_field_int(delay, UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(transfer_data,  UVM_ALL_ON + UVM_HEX)
    `uvm_field_int(monitor_data,   UVM_ALL_ON + UVM_HEX)
    `uvm_field_int(output_enable,  UVM_ALL_ON + UVM_HEX)
    `uvm_field_string(agent,       UVM_ALL_ON + UVM_NOCOMPARE)
  `uvm_object_utils_end

     
  // This requires for registration of the ptp_tx_frame   
  function new(string name = "gpio_transfer");
	  super.new(name);
  endfunction 
   

endclass : gpio_transfer

`endif
