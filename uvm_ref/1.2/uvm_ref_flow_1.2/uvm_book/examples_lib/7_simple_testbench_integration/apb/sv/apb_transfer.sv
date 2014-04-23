/*******************************************************************************
  FILE : apb_transfer.svh
*******************************************************************************/
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


//------------------------------------------------------------------------------
// CLASS: apb_transfer declaration
//------------------------------------------------------------------------------

class apb_transfer extends uvm_sequence_item;                                  

  rand bit [31:0]           addr;
  rand apb_direction_enum   direction;
  rand bit [7:0]            data;
  rand int unsigned         transmit_delay;
  string                    master;
  string                    slave;
   
  constraint c_direction { direction inside { APB_READ, APB_WRITE }; }
 
  constraint c_transmit_delay { transmit_delay <= 10 ; }

  `uvm_object_utils_begin(apb_transfer)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_enum(apb_direction_enum, direction, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_string(master, UVM_DEFAULT|UVM_NOCOMPARE)
    `uvm_field_string(slave, UVM_DEFAULT|UVM_NOCOMPARE)
  `uvm_object_utils_end

  function new (string name = "apb_transfer");
    super.new(name);
  endfunction

endclass : apb_transfer
