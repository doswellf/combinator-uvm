/*-----------------------------------------------------------------
File name     : demo_tb.sv
Developers    : Kathleen Meade
Created       : May 16, 2010
Description   : Simple Testbench to understand the APB UVC
Notes         :
-------------------------------------------------------------------
Copyright 2010 (c) Cadence Design Systems
-----------------------------------------------------------------*/

`ifndef DEMO_TB_SV
`define DEMO_TB_SV

//`include "apb_demo_scoreboard.sv"
`include "demo_config.sv"
`include "apb_master_seq_lib.sv"
`include "apb_slave_seq_lib.sv"

//------------------------------------------------------------------------------
// CLASS: apb_demo_tb
//------------------------------------------------------------------------------

class demo_tb extends uvm_env;

  // Provide UVM automation and utility methods
  `uvm_component_utils(demo_tb)

  // apb environment
  apb_env apb0;

  // configuration object
  demo_config demo_cfg;

  // Scoreboard to check the memory operation of the slave.
  //apb_demo_scoreboard scoreboard0;

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : demo_tb

  // UVM build_phase
  function void demo_tb::build_phase(uvm_phase phase);
    super.build_phase(phase);
    demo_cfg = demo_config::type_id::create("demo_cfg");     
    uvm_config_object::set(this, "apb0*", "cfg", demo_cfg);
    uvm_config_object::set(this, "apb0.slave[0]*", "cfg", demo_cfg.slave_configs[0]);
    uvm_config_object::set(this, "apb0.slave[1]*", "cfg", demo_cfg.slave_configs[1]);
    apb0 = apb_env::type_id::create("apb0", this);

   //Create Scoreboard - 
   // scoreboard0 = apb_demo_scoreboard::type_id::create("scoreboard0", this);
  endfunction : build_phase

  // UVM connect_phase
  function void demo_tb::connect_phase(uvm_phase phase);
    //Connect slave monitor to scoreboard
   // apb0.slaves[0].monitor.item_collected_port.connect(scoreboard0.item_collected_imp);
    // Set up slaves address map for apb0
    //apb0.set_slave_address_map("slaves[0]",0 ,32'h0fffffff);
    //apb0.set_slave_address_map("slaves[1]",32'h10000000, 32'hffffffff);
  endfunction : connect_phase

`endif // DEMO_TB_SV
