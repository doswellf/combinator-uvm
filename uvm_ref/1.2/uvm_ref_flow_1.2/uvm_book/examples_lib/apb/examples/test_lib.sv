/*-----------------------------------------------------------------
File name     : test_lib.sv
Developers    : Kathleen Meade
Created       : Tue May  4 15:13:46 2010
Description   :
Notes         :
-------------------------------------------------------------------
Copyright 2010 (c) Cadence Design Systems
-----------------------------------------------------------------*/

`include "./examples/demo_tb.sv"

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
     //uvm_config_int::set(this, "demo_tb0.apb0.bus_monitor", "coverage_enable", 0);
     //uvm_config_int::set(this, "*", "coverage_enable", 0);
    // Create the tb
    demo_tb0 = demo_tb::type_id::create("demo_tb0", this);
  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    //EXAMPLE: Set verbosity for the bus monitor
    //demo_tb0.apb0.monitor.set_report_verbosity_level(UVM_FULL);
  endfunction : connect_phase

//function void end_of_elaboration_phase(uvm_phase phase);
//  super.end_of_elaboration_phase(phase);
//  this.print();   // prints the test hierarchy
//endfunction : end_of_elaboration_phase

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
    uvm_config_db #(uvm_object_wrapper)::set(this,
       "demo_tb0.apb0.master.sequencer.run_phase",
       "default_sequence", read_after_write_seq::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this,
       "demo_tb0.apb0.slave[0].sequencer.run_phase",
       "default_sequence", mem_response_seq::type_id::get());
    // Create the tb
    super.build_phase(phase);
  endfunction : build_phase

endclass : test_read_after_write

//----------------------------------------------------------------
// TEST: test_seq_lib
//----------------------------------------------------------------
class test_seq_lib extends demo_base_test;

  `uvm_component_utils(test_seq_lib)

  function new(string name = "test_seq_lib", uvm_component parent);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    uvm_sequence_library_cfg seqlib_cfg;
    // Set the default sequence for the master and slaves
    uvm_config_db #(uvm_object_wrapper)::set(this, "demo_tb0.apb0.master.sequencer.run_phase",
                          "default_sequence", demo_seq_lib2::type_id::get());

    //selection mode: UVM_SEQ_LIB_RAND, UVM_SEQ_LIB_RANDC, UVM_SEQ_LIB_ITEM, UVM_SEQ_LIB_USER
    //Constructor args:  name,       selection_mode,  min_random_count, max_random_count
    seqlib_cfg = new("seqlib_cfg", UVM_SEQ_LIB_RAND,     10,            10);
    uvm_config_db #(uvm_sequence_library_cfg)::set(this,
                    "demo_tb0.apb0.master.sequencer.run_phase",
                    "default_sequence.config", seqlib_cfg);

    // OR - configure independently:
    // Set the selection mode: UVM_SEQ_LIB_RAND, UVM_SEQ_LIB_RANDC, UVM_SEQ_LIB_ITEM, UVM_SEQ_LIB_USER
    //uvm_config_db #(uvm_sequence_lib_mode)::set(this, "demo_tb0.apb0.master.sequencer.run_phase",
    //                      "default_sequence.selection_mode", UVM_SEQ_LIB_RANDC);
    //uvm_config_db#(int unsigned)::set(this, "demo_tb0.apb0.master.sequencer.run_phase",
    //                      "default_sequence.min_random_count", 4);
    //uvm_config_db#(int unsigned)::set(this, "demo_tb0.apb0.master.sequencer.run_phase",
    //                      "default_sequence.max_random_count", 8);

    uvm_config_db#(uvm_object_wrapper)::set(this,"demo_tb0.apb0.slave[0].sequencer.run_phase",
                          "default_sequence", mem_response_seq::type_id::get());
    // Create the tb
    super.build_phase(phase);
  endfunction : build_phase

endclass : test_seq_lib

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

//----------------------------------------------------------------
// TEST: config_uart_ctrl_test
//----------------------------------------------------------------
class config_uart_ctrl_test extends uvm_test;

  `uvm_component_utils(config_uart_ctrl_test)

  demo_tb demo_tb0;
  uvm_table_printer printer;

  function new(string name = "config_uart_ctrl_test", 
    uvm_component parent);
    super.new(name,parent);
    printer = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Enable transaction recording for everything
    set_config_int("*", "recording_detail", UVM_FULL);
    demo_tb0 = demo_tb::type_id::create("demo_tb0", this);
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    apb_transfer transfer;
    uvm_sequence_base seq;
    phase.raise_objection(this, "Test: config_uart_ctrl_test");
    printer.knobs.depth = 5;
    this.print(printer);
    seq = new();
    seq.set_sequencer(demo_tb0.apb0.master.sequencer);
    transfer = apb_transfer::type_id::create("transfer", this);
    transfer.set_sequencer(demo_tb0.apb0.master.sequencer);
    transfer.set_sequencer(demo_tb0.apb0.master.sequencer);
    #100  // wait for reset to be finished
    // Set the Line Control Reg to 8'h83;
    transfer.addr = 8'h03;
    transfer.data = 8'h83;
    transfer.direction = APB_WRITE;
    transfer.transmit_delay = 1;
    //demo_tb0.apb0.master.sequencer.execute_item(transfer);
    seq.start_item(transfer); seq.finish_item(transfer);
    // Set the Div Latch1 Reg to 8'h00;
    transfer.addr = 8'h00;
    transfer.data = 8'h01;
    //demo_tb0.apb0.master.sequencer.execute_item(transfer);
    seq.start_item(transfer); seq.finish_item(transfer);
    // Set the Div Latch2 Reg to 8'h01;
    transfer.addr = 8'h01;
    transfer.data = 8'h00;
    //demo_tb0.apb0.master.sequencer.execute_item(transfer);
    seq.start_item(transfer); seq.finish_item(transfer);
    // Set the Line Control Reg to 8'h03;
    transfer.addr = 8'h03;
    transfer.data = 8'h03;
    //demo_tb0.apb0.master.sequencer.execute_item(transfer);
    seq.start_item(transfer); seq.finish_item(transfer);
    // Use the drain time for this phase
    phase.drop_objection(this, "Test: config_uart_ctrl_test");
  endtask : run_phase

endclass : config_uart_ctrl_test
