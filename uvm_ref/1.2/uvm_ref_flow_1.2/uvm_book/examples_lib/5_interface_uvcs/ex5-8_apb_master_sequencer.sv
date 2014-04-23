/**************************************************************************
  Example 5-8: APB Master Sequencer

  To run:   %  irun -uvm ex5-8_apb_master_sequencer.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-8_apb_master_sequencer.sv
**************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"
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
