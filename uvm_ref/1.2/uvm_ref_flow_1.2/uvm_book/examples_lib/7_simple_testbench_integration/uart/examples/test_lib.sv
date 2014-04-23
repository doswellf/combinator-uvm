/*-----------------------------------------------------------------
File name     : test_lib.sv
Developers    : Kathleen Meade
Created       : Tue May  4 15:13:46 2010
Description   :
Notes         :
-------------------------------------------------------------------
Copyright 2010 (c) Cadence Design Systems
-----------------------------------------------------------------*/

`include "demo_tb.sv"

//----------------------------------------------------------------
//
// TEST: demo_base_test - Base test
//
//----------------------------------------------------------------
class demo_base_test extends uvm_test;

  `uvm_component_utils(demo_base_test)

  demo_tb demo_tb0;
  uvm_table_printer printer;

  function new(string name = "demo_base_test", 
    uvm_component parent);
    super.new(name,parent);
    printer = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Enable transaction recording for everything
    //set_config_int("*", "recording_detail", UVM_FULL);
    // Create the tb
    demo_tb0 = demo_tb::type_id::create("demo_tb0", this);
  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    // Set verbosity for the bus monitor
    //demo_tb0.uart0.bus_monitor.set_report_verbosity_level(UVM_FULL);
  endfunction : connect_phase

  task run_phase(uvm_phase phase);
    //printer.knobs.depth = 5;
    this.print(printer);
   // Use the drain time for this phase
   phase.phase_done.set_drain_time(this, 200);
  endtask : run_phase

endclass : demo_base_test

//----------------------------------------------------------------
//
// TEST: uart_sequence_test
//
//----------------------------------------------------------------
class uart_sequence_test extends demo_base_test;

  `uvm_component_utils(uart_sequence_test)

  function new(string name = "uart_sequence_test", uvm_component parent);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    // Set the default sequence for the tx and rx
    uvm_config_db#(uvm_object_wrapper)::set(this, "demo_tb0.uart0.Tx.sequencer.run_phase","default_sequence",uart_incr_payload_seq::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "demo_tb0.uart0.Rx.sequencer.run_phase","default_sequence", uart_short_transmit_seq::type_id::get());
    // Create the tb
    super.build_phase(phase);
  endfunction : build_phase

endclass : uart_sequence_test
