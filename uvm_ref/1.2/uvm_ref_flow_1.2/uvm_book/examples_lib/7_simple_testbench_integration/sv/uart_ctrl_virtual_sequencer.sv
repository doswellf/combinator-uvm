/*-------------------------------------------------------------------------
File name   : uart_ctrl_virtual_sequencer.sv
Title       : Virtual sequencer
Project     :
Created     :
Description : This file implements the Virtual sequencer for APB-UART environment
Notes       : 
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

class uart_ctrl_virtual_sequencer extends uvm_sequencer;

    apb_pkg::apb_master_sequencer apb_seqr;
    uart_pkg::uart_sequencer uart_seqr;
   
    // Uart Controller configuration object
    uart_ctrl_config cfg;

    function new (input string name="uart_ctrl_virtual_sequencer", input uvm_component parent=null);
      super.new(name, parent);
    endfunction : new

    `uvm_component_utils_begin(uart_ctrl_virtual_sequencer)
       `uvm_field_object(cfg, UVM_DEFAULT | UVM_NOPRINT)
    `uvm_component_utils_end

endclass : uart_ctrl_virtual_sequencer
