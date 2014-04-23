// IVB checksum: 2834038605
/*-----------------------------------------------------------------
File name     : ahb_slave_sequencer.sv
Created       : Wed May 19 15:42:21 2010
Description   : This file declares the sequencer the slave.
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


`ifndef AHB_SLAVE_SEQUENCER_SV
`define AHB_SLAVE_SEQUENCER_SV

//------------------------------------------------------------------------------
//
// CLASS: ahb_slave_sequencer
//
//------------------------------------------------------------------------------

class ahb_slave_sequencer extends uvm_sequencer #(ahb_transfer);

  // The virtual interface used to drive and view HDL signals.
  // This OPTIONAL connection is only needed if the sequencer needs
  // access to the interface directly.
  // If you remove it - you will need to modify the agent as well
  virtual interface ahb_if vif;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils(ahb_slave_sequencer)

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass : ahb_slave_sequencer

`endif // AHB_SLAVE_SEQUENCER_SV

