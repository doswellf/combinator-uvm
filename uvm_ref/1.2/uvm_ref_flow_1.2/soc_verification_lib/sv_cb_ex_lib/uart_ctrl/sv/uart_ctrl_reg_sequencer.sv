/*-----------------------------------------------------------------
File name     : uart_ctrl_reg_sequencer.sv
Created       : Fri Mar 9 2012
Description   :
Notes         : 
-------------------------------------------------------------------
Copyright 2012 (c) Cadence Design Systems
-----------------------------------------------------------------*/

//------------------------------------------------------------------------------
// CLASS: uart_ctrl_reg_sequencer
//------------------------------------------------------------------------------
class uart_ctrl_reg_sequencer extends uvm_sequencer;

  uart_ctrl_reg_model_c reg_model;

  `uvm_component_utils_begin(uart_ctrl_reg_sequencer)
     `uvm_field_object(reg_model, UVM_DEFAULT | UVM_REFERENCE)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass : uart_ctrl_reg_sequencer
