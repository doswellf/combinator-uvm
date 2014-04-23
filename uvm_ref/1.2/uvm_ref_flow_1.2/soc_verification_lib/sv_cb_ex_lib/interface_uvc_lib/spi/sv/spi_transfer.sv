/*-------------------------------------------------------------------------
File name   : spi_transfer.sv
Title       : SPI SystemVerilog UVM UVC
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


`ifndef SPI_TRANSFER_SV
`define SPI_TRANSFER_SV

class spi_transfer extends uvm_sequence_item;

  rand int unsigned delay;

  rand bit [31:0] transfer_data;
  bit [31:0] receive_data;

  string agent = "";        //updated my monitor - scoreboard can use this

  constraint c_default_delay {delay >= 0; delay < 20;}

  // These declarations implement the create() and get_type_name() as well as enable automation of the
  // transfer fields   
  `uvm_object_utils_begin(spi_transfer)
    `uvm_field_int(delay, UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(transfer_data,  UVM_ALL_ON + UVM_HEX)
    `uvm_field_int(receive_data,   UVM_ALL_ON + UVM_HEX)
    `uvm_field_string(agent,       UVM_ALL_ON + UVM_NOCOMPARE)
  `uvm_object_utils_end

     
  // This requires for registration of the ptp_tx_frame   
  function new(string name = "spi_transfer");
	  super.new(name);
  endfunction 
   

endclass : spi_transfer

`endif
