/*-----------------------------------------------------------------
File name     : simple_top.sv
Developers    : Kathleen Meade
Created       : Nov 2 2012
Description   :
Notes         :
-------------------------------------------------------------------
Copyright 2012 (c) Cadence Design Systems
-----------------------------------------------------------------*/
`define APB_ADDR_WIDTH 32

`include "./apb_if.sv"
`include "./apb_pkg.sv"
module simple_top;

  // Import the UVM Package
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Import the APB OVC Package
  import apb_pkg::*;

  // Include the sequence libraries
  `include "./apb_master_seq_lib.sv"
  `include "./apb_slave_seq_lib.sv"

  // Create a simple test  
  class simple_test extends uvm_test;

    `uvm_component_utils(simple_test)

    // apb environment
    apb_env apb0;

    // configuration object
    apb_config cfg;

    function new(string name = "simple_test", uvm_component parent);
      super.new(name,parent);
    endfunction : new

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Create the configuration object
      cfg = apb_config::type_id::create("cfg");     

      // configure APB with an ACTIVE master and one ACTIVE slave
      cfg.add_slave("slave[0]", 32'h0000_0000, 32'hFFFF_FFFF, 0, UVM_ACTIVE);
      cfg.add_master("master", UVM_ACTIVE);
      // SET the config upject for the master/slave
      uvm_config_object::set(this, "apb0*", "cfg", cfg);
      uvm_config_object::set(this, "apb0.slave[0]*", "cfg", cfg.slave_configs[0]);
  
      // Set the default sequence for the master and slave
      uvm_config_db#(uvm_object_wrapper)::set(this,
                      "apb0.master.sequencer.run_phase",
                      "default_sequence",
                       multiple_read_after_write_seq::type_id::get());
      uvm_config_db#(uvm_object_wrapper)::set(this,
                      "apb0.slave[0].sequencer.run_phase",
                      "default_sequence",
                       mem_response_seq::type_id::get());
 
      // Now CREATE the APB UVC
      apb0 = apb_env::type_id::create("apb0", this);
    endfunction : build_phase

    task run_phase(uvm_phase phase);
      this.print();
      //EXAMPLE Use the drain time for this phase
      phase.phase_done.set_drain_time(this, 200);
    endtask : run_phase
  endclass : simple_test

  reg clock;
  reg reset;

  apb_if apb_if_0(clock, reset);
  
  initial begin
    // Set virtual interface for this test
    uvm_config_db#(virtual apb_if)::set(null, "*.apb0*", "vif", apb_if_0);
    run_test();
  end

  //Generate Reset and Clock
  initial begin
    reset <= 1'b0;
    clock <= 1'b0;
    #51 reset = 1'b1;
  end

  always  #5 clock = ~clock;

endmodule
