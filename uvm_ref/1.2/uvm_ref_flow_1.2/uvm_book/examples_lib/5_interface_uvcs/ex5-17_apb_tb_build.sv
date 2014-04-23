/*******************************************************************************
  Example 5-17: Testbench build() Method Overrides the Default APB Configuration

  To run:   %  irun -uvm ex5-17_apb_tb_build.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-17_apb_tb_build.sv
*******************************************************************************/
`include "sv/apb_if.sv"
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "sv/apb_transfer.sv"
`include "sv/apb_config.sv"
`include "sv/apb_bus_monitor.sv"
`include "sv/apb_monitor.sv"
`include "sv/apb_collector.sv"
`include "sv/apb_master_driver.sv"
`include "sv/apb_master_sequencer.sv"
`include "sv/apb_master_agent.sv"
`include "sv/apb_slave_driver.sv"
`include "sv/apb_slave_sequencer.sv"
`include "sv/apb_slave_agent.sv"
`include "sv/apb_env1.sv"

class demo_config extends apb_config;
  `uvm_object_utils(demo_config)

  function new(string name = "demo_config");
    super.new(name);
    add_slave("slave0", 32'h0000_0000, 32'h7FFF_FFFF, 0, UVM_ACTIVE);
    add_slave("slave1", 32'h8000_0000, 32'hFFFF_FFFF, 1, UVM_PASSIVE);
    add_master("master", UVM_ACTIVE);
  endfunction

endclass : demo_config

// Simple testbench class
class demo_tb extends uvm_env;
  `uvm_component_utils(demo_tb)
  apb_env apb0;
  demo_config demo_cfg;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    demo_cfg = demo_config::type_id::create("demo_cfg");
    uvm_config_object::set(this, "apb0", "cfg", demo_cfg);
    apb0 = apb_env::type_id::create("apb0", this);
  endfunction : build_phase

  function void start_of_simulation_phase(uvm_phase phase);
    this.print();
    uvm_test_done.set_drain_time(this, 100);
  endfunction : start_of_simulation_phase
endclass : demo_tb

bit clk, reset;

apb_if apb_if0 (clk, reset);

demo_tb tb;

initial begin
  uvm_config_db#(virtual apb_if)::set(null, "*", "vif", apb_if0);
  tb = demo_tb::type_id::create("tb", null);
  run_test();
end

initial
  #100 global_stop_request();

endmodule : test
