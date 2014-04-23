/****************************************************************
  Example 8-1: Using p_sequencer in a sequence

  To run:   %  irun -uvm ex8-1_interrupt.sv \
               -incdir ../7_simple_testbench_integration/apb
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "sv/apb_if.sv"
`include "sv/apb_pkg.sv"

import apb_pkg::*;
`define CISR_REG 8'h02

class apb_interrupt_from_uart extends apb_master_base_seq;

  `uvm_object_utils(apb_interrupt_from_uart)
  `uvm_declare_p_sequencer(apb_master_sequencer)

  function new(string name="apb_interrupt_from_uart");
    super.new(name);
  endfunction : new

  // Sequence body
  virtual task body();
    forever begin
     @(p_sequencer.vif.ua_int);
     `uvm_info("INTERRUPT_SEQ", "Executing Sequence", UVM_LOW)
     grab(p_sequencer);
     `uvm_do_with(req, { addr == `CISR_REG; direction == APB_READ; })
     if (req.data[1]) `uvm_info("INTERRUPT", "Rx EMPTY Interrupt occurred", UVM_LOW)
     if (req.data[2]) `uvm_info("INTERRUPT", "Rx FULL Interrupt occurred", UVM_LOW)
     if (req.data[3]) `uvm_info("INTERRUPT", "Tx EMPTY Interrupt occurred", UVM_LOW)
     if (req.data[4]) `uvm_info("INTERRUPT", "Tx FULL Interrupt occurred", UVM_LOW)
     // do something else
     ungrab(p_sequencer);
    end
  endtask : body

endclass : apb_interrupt_from_uart
