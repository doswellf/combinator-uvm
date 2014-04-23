/*-----------------------------------------------------------------
File name     : simple_test.sv
Developers    : Kathleen Meade
Created       : Nov 2, 2012
Description   : Simple Testbench and Test for the APB UVC
-------------------------------------------------------------------
Copyright 2012 (c) Cadence Design Systems
-----------------------------------------------------------------*/
`include "sv/apb_master_seq_lib.sv"
`include "sv/apb_slave_seq_lib.sv"
//------------------------------------------------------------------------------
// CLASS: simple_tb
//------------------------------------------------------------------------------
class simple_tb extends uvm_env;

  // Provide UVM automation and utility methods
  `uvm_component_utils(simple_tb)

  // apb environment
  apb_env apb0;

  // configuration object
  apb_config cfg;

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // UVM build_phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cfg = apb_config::type_id::create("cfg");     
    // configure APB with an ACTIVE master and one ACTIVE slave
    cfg.add_slave("slave[0]", 32'h0000_0000, 32'hFFFF_FFFF, 0, UVM_ACTIVE);
    cfg.add_master("master", UVM_ACTIVE);
    cfg.print();  //KATHLEEN REMOVE THIS
    // SET the config upject for the master/slave
    uvm_config_object::set(this, "apb0*", "cfg", cfg);
    uvm_config_object::set(this, "apb0.slave[0]*", "cfg", cfg.slave_configs[0]);
    apb0 = apb_env::type_id::create("apb0", this);
  endfunction : build_phase

endclass : simple_tb

//-----------------------------------------------------
// CLASS:  simple_test - the test
//-----------------------------------------------------
class simple_test extends uvm_test;

  `uvm_component_utils(simple_test)

  // Instance of the testbench
  simple_tb tb0;

  function new(string name = "simple_test", uvm_component parent);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Disable coverage
    uvm_config_int::set(this, "*", "coverage_enable", 0);
    // Set the default sequence for the master and slave
    uvm_config_db #(uvm_object_wrapper)::set(this,
                    "tb0.apb0.master.sequencer.run_phase",
                    "default_sequence",
                     multiple_read_after_write_seq::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this,
                    "tb0.apb0.slave[0].sequencer.run_phase",
                    "default_sequence",
                     mem_response_seq::type_id::get());

    // Create the tb
    tb0 = simple_tb::type_id::create("tb0", this);
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    this.print();
    //EXAMPLE Use the drain time for this phase
    phase.phase_done.set_drain_time(this, 200);
  endtask : run_phase

endclass : simple_test
