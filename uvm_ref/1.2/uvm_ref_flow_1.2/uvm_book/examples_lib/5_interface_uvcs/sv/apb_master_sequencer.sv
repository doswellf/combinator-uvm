/*****************************************************************************
  FILE : apb_master_sequencer.sv
*****************************************************************************/
//------------------------------------------------------------------------------
// CLASS: apb_master_sequencer declaration
//------------------------------------------------------------------------------

class apb_master_sequencer extends uvm_sequencer #(apb_transfer);

  // UVM automation macro for sequencers
  `uvm_component_utils(apb_master_sequencer)

  // Constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass : apb_master_sequencer
