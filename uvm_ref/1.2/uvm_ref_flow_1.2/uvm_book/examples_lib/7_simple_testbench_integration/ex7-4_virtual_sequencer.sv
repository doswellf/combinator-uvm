/****************************************************************
  Example 7-4: UART Controller Virtual Sequencer

  This file is also located in sv/uart_ctrl_virtual_sequencer.sv
  No testcase to run for this
****************************************************************/
/*-------------------------------------------------------------------------
File name   : uart_ctrl_virtual_sequencer.sv
Title       : Virtual sequencer
Project     :
Created     :
Description : This file implements the Virtual sequencer for
              UART Controller environment
Notes       : 
----------------------------------------------------------------------*/
class uart_ctrl_virtual_sequencer extends uvm_sequencer;

    apb_master_sequencer apb_seqr;
    uart_sequencer       uart_seqr;
   
    function new (input string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    `uvm_component_utils(uart_ctrl_virtual_sequencer)

endclass : uart_ctrl_virtual_sequencer
