/*-------------------------------------------------------------------------
File name   : uart_sequencer.sv
Title       : Sequencer file for the UART UVC
Project     :
Created     :
Description : The sequencer generates stream in transaction in term of items 
              and sequences of item
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

`ifndef UART_SEQUENCER_SVH
`define UART_SEQUENCER_SVH

class uart_sequencer extends uvm_sequencer #(uart_frame);

  virtual interface uart_if vif;

  uart_config cfg;

  `uvm_component_utils_begin(uart_sequencer)
    `uvm_field_object(cfg, UVM_DEFAULT | UVM_REFERENCE)
  `uvm_component_utils_end

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction 

  // UVM build_phase
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if(cfg == null)
        if (!uvm_config_db#(uart_config)::get(this, "", "cfg", cfg))
          `uvm_warning("NOCONFIG", "uart_config not set for this component")
  endfunction : build_phase

endclass : uart_sequencer
`endif // UART_SEQUENCER_SVH
