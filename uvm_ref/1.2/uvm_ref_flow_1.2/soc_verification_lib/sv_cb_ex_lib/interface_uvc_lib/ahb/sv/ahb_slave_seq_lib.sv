// IVB checksum: 2593477727
/*-----------------------------------------------------------------
File name     : ahb_slave_seq_lib.sv
Created       : Wed May 19 15:42:21 2010
Description   : This file implements several sequence kinds
Notes         : Each sequence implements a typical scenario or a
              : combination of existing scenarios.
              : Cadence recommends defining reusable sequences in 
              : this directory and project-specific sequences in the
              : project directory ("examples").
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


`ifndef AHB_SLAVE_SEQ_LIB_SV
`define AHB_SLAVE_SEQ_LIB_SV

//------------------------------------------------------------------------------
//
// SEQUENCE: ahb_slave_resp_seq
//
//------------------------------------------------------------------------------
 
class ahb_slave_resp_seq extends uvm_sequence #(ahb_transfer);

  // Required macro for sequences automation
  `uvm_object_utils(ahb_slave_resp_seq)
  `uvm_declare_p_sequencer(ahb_slave_sequencer)    
  
  // Constructor
  function new(string name="ahb_slave_resp_seq");
    super.new(name);
  endfunction
  
  // Sequence body definition
  virtual task body();
    `uvm_info(get_type_name(),"Executing... (forever)", UVM_HIGH)
    // Allocate once
    `uvm_create(rsp)
    forever begin
      // Randomize and send many times
      `uvm_rand_send(rsp)
    end
  endtask : body
  
endclass : ahb_slave_resp_seq
 
`endif // AHB_SLAVE_SEQ_LIB_SV
