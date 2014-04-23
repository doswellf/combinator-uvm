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

//`include "demo_scoreboard.sv"
`include "demo_config.sv"
//`include "uart_seq_lib.sv"  // incl in package

//------------------------------------------------------------------------------
// CLASS: demo_tb
//------------------------------------------------------------------------------

class demo_tb extends uvm_env;

  // Provide UVM automation and utility methods
  `uvm_component_utils(demo_tb)

  // UART environment
  uart_env uart0;

  // configuration object
  demo_config demo_cfg;

  // Scoreboard 
  //demo_scoreboard scoreboard0;

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : demo_tb

  // UVM build() phase
  function void demo_tb::build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create the configuration object
    demo_cfg = demo_config::type_id::create("demo_cfg");     
    if (!demo_cfg.randomize()) `uvm_error("RNDFAIL", "Demo Config Randomization")
    demo_cfg.print();
    uvm_config_object::set(this, "uart0*", "cfg", demo_cfg);
    uart0 = uart_env::type_id::create("uart0", this);

  endfunction : build_phase

  // UVM connect() phase
  function void demo_tb::connect_phase(uvm_phase phase);
  endfunction : connect_phase

`endif // DEMO_TB_SV
