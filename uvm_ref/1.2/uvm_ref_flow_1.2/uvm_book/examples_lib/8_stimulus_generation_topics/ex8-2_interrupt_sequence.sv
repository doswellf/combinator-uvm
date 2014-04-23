/****************************************************************
  Example 8-2: Handling interrupts using Sequences

  To run:   %  irun -uvm  \
               -incdir ../7_simple_testbench_integration/apb \
               ex8-2_interrupt_sequence.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_types.sv"
`include "sv/apb_transfer.sv"

typedef class apb_master_sequencer;
//----------------------------------------------------------
// SEQUENCE: read_status_seq - reads a status register
//----------------------------------------------------------
class read_status_seq extends uvm_sequence #(apb_transfer);

  `uvm_object_utils(read_status_seq)
  `uvm_declare_p_sequencer(apb_master_sequencer)

  function new(string name="read_status_seq");
    super.new(name);
  endfunction : new

  task body();
    `uvm_info("RD_STATUS_REG_SEQ", "Executing...", UVM_LOW)
    // Sequence details go here
  endtask : body
endclass : read_status_seq

//----------------------------------------------------------
// SEQUENCE: interrput_handler_seq: ON interrupt, grab the
// sequencer and execute a read_status_seq sequence.
//----------------------------------------------------------
class interrupt_handler_seq extends uvm_sequence #(apb_transfer);

  `uvm_object_utils(interrupt_handler_seq)
  `uvm_declare_p_sequencer(apb_master_sequencer)

  // Sequence to be called upon interrupt
  read_status_seq interrupt_reset_seq;

  // Sequence body
  virtual task body();
    forever begin
     @(p_sequencer.interrupt);
     `uvm_info("INTERRUPT_SEQ", "Executing Sequence", UVM_LOW)
     grab(p_sequencer);
     `uvm_do(interrupt_reset_seq)
     ungrab(p_sequencer);
    end
  endtask : body

  // Constructor
  function new(string name="interrupt_handler_seq");
    super.new(name);
  endfunction

endclass : interrupt_handler_seq

class apb_master_sequencer extends uvm_sequencer #(apb_transfer);
 
  `uvm_component_utils(apb_master_sequencer)

  interrupt_handler_seq interrupt_seq;
  event interrupt;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual task run();
    interrupt_seq = interrupt_handler_seq::type_id::create("interrupt_seq");
    fork
      interrupt_seq.start(this);
    join_none
    super.run();
  endtask : run

endclass : apb_master_sequencer
