/****************************************************************
  Example 5-13a: Simple APB Env Test

  To run:   %  irun -uvm ex5-13a_test_env.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-13a_test_env.sv
****************************************************************/

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
`include "sv/apb_env0.sv"

class env_test extends uvm_test;

  apb_env env;

  `uvm_component_utils(env_test)

  function new(string name="env_test", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    env = apb_env::type_id::create("env", this);
  endfunction : build_phase

  function void start_of_simulation_phase(uvm_phase phase);
    this.print();
    uvm_test_done.set_drain_time(this, 100);
  endfunction : start_of_simulation_phase
endclass : env_test

bit clk, reset;

apb_if apb_if0 (clk, reset);

initial begin
  uvm_config_db#(virtual apb_if)::set(null, "*", "vif", apb_if0);
  run_test("env_test");
end

endmodule : test
