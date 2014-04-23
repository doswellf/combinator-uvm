// IVB checksum: 278368784
/*-----------------------------------------------------------------
File name     : ahb_master_seq_lib.sv
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


`ifndef AHB_MASTER_SEQ_LIB_SV
`define AHB_MASTER_SEQ_LIB_SV

//------------------------------------------------------------------------------
//
// SEQUENCE: ahb_master_transfer_seq
//
//------------------------------------------------------------------------------
 
class ahb_master_transfer_seq extends uvm_sequence #(ahb_transfer);
  
  // Parameter for this sequence
  rand bit [31:0] s_data;

  // Required macro for sequences automation
  `uvm_object_utils(ahb_master_transfer_seq)
  `uvm_declare_p_sequencer(ahb_master_sequencer)    

  // Constructor
  function new(string name="ahb_master_transfer_seq");
    super.new(name);
  endfunction

  // Sequence body definition
  virtual task body();
    begin
      `uvm_info(get_type_name(), "Executing...", UVM_HIGH)
      `uvm_do_with(req, { req.data == s_data; } )
    end
  endtask
  
endclass : ahb_master_transfer_seq

//------------------------------------------------------------------------------
//
// SEQUENCE: ahb_master_nested_seq
//
//------------------------------------------------------------------------------
 
class ahb_master_nested_seq extends uvm_sequence #(ahb_transfer);

  // Sequence that will be called in this sequence
  ahb_master_transfer_seq ahb_seq;

  // Required macro for sequences automation
  `uvm_object_utils(ahb_master_nested_seq)
  `uvm_declare_p_sequencer(ahb_master_sequencer)    

  // Parameter for this sequence
  rand int itr;

  // Sequence Constraints
  constraint itr_size_ct { itr inside {[1:8]}; }

  // Constructor
  function new(string name="ahb_master_nested_seq");
    super.new(name);
  endfunction
  
  // Sequence body definition
  virtual task body();
    begin
      `uvm_info(get_type_name(),
         $sformatf("Executing... (%0d ahb_master_transfer sequences)",itr), UVM_HIGH)
      void'(p_sequencer.get_config_int("ahb_master_nested_seq.itr", itr));
      for(int i = 0; i < itr; i++) begin
        `uvm_do(ahb_seq)
      end
    end
  endtask
  
endclass : ahb_master_nested_seq

`endif // AHB_MASTER_SEQ_LIB_SV
