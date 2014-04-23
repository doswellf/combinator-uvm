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
    set_config_int("*", "recording_detail", UVM_FULL);
    // EXAMPLE: disable coverage for the bus_monitor
     //set_config_int("demo_tb0.apb0.bus_monitor", "coverage_enable", 0);
     uvm_config_int::set(this, "demo_tb0.apb0.bus_monitor", "coverage_enable", 0);
     //uvm_config_int::set(this, "*", "coverage_enable", 0);
    // Create the tb
    demo_tb0 = demo_tb::type_id::create("demo_tb0", this);
  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    //EXAMPLE: Set verbosity for the bus monitor
    //demo_tb0.apb0.monitor.set_report_verbosity_level(UVM_FULL);
  endfunction : connect_phase

  task run_phase(uvm_phase phase);
    printer.knobs.depth = 5;
    this.print(printer);
    // Use the drain time for this phase
    phase.phase_done.set_drain_time(this, 200);
  endtask : run_phase

endclass : demo_base_test
//----------------------------------------------------------------
// TEST: test_write_read
//----------------------------------------------------------------
class test_read_after_write extends demo_base_test;

  `uvm_component_utils(test_read_after_write)

  function new(string name = "test_read_after_write", uvm_component parent);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    // Set the default sequence for the master and slaves
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.master.sequencer.run_phase",
                          "default_sequence", read_after_write_seq::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this,"demo_tb0.apb0.slave[0].sequencer.run_phase",
                          "default_sequence", mem_response_seq::type_id::get());
    // Create the tb
    super.build_phase(phase);
  endfunction : build_phase

endclass : test_read_after_write

//----------------------------------------------------------------
// TEST: test_multiple_read_after_write
//----------------------------------------------------------------
class test_multiple_read_after_write extends demo_base_test;

  `uvm_component_utils(test_multiple_read_after_write)

  function new(string name = "test_multiple_read_after_write", uvm_component parent);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    // Set the default sequence for the master and slaves
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.master.sequencer.run_phase",
                          "default_sequence", multiple_read_after_write_seq::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this,"demo_tb0.apb0.slave[0].sequencer.run_phase",
                          "default_sequence", mem_response_seq::type_id::get());
    // Create the tb
    super.build_phase(phase);
  endfunction : build_phase

endclass : test_multiple_read_after_write


//----------------------------------------------------------------
// TEST: test_048_write_read
//----------------------------------------------------------------
class test_048_write_read extends demo_base_test;

  `uvm_component_utils(test_048_write_read)

  function new(string name = "test_048_write_read", uvm_component parent);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    begin //TEMPORARY: Required for IUS
    // Set the default sequence for the master and slaves
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.master.sequencer.run_phase","default_sequence", multiple_read_after_write_seq::type_id::get());
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.slave[0].sequencer.run_phase","default_sequence", mem_response_seq::type_id::get());
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.slave[1].sequencer.run_phase","default_sequence", mem_response_seq::type_id::get());
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.slave[2].sequencer.run_phase","default_sequence", simple_response_seq::type_id::get());
    // Create the tb
    super.build_phase(phase);
    end
  endfunction : build_phase

endclass : test_048_write_read
