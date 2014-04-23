/*******************************************************************************
  FILE : apb_slave_sequencer.sv
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

                                                                                
`ifndef APB_SLAVE_SEQUENCER_SV
`define APB_SLAVE_SEQUENCER_SV

//------------------------------------------------------------------------------
// CLASS: apb_slave_sequencer declaration
//------------------------------------------------------------------------------

class apb_slave_sequencer extends uvm_sequencer #(apb_transfer);

  uvm_blocking_peek_port#(apb_transfer) addr_trans_port;

  apb_slave_config cfg;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_slave_sequencer)
    `uvm_field_object(cfg, UVM_DEFAULT|UVM_REFERENCE)
  `uvm_component_utils_end

  // Constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
    addr_trans_port = new("addr_trans_port", this);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(cfg == null)
      if (!uvm_config_db#(apb_slave_config)::get(this, "", "cfg", cfg))
      `uvm_error("NOCONFIG", "No configuration set")
  endfunction : build_phase

endclass : apb_slave_sequencer

`endif // APB_SLAVE_SEQUENCER_SV
