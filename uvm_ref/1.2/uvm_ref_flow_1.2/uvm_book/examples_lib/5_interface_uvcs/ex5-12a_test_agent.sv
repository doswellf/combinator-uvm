/****************************************************************
  Example 5-12a: Simple APB Agent Test

  To run:   %  irun -uvm ex5-12a_test_agent.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-12a_test_agent.sv
****************************************************************/
`include "sv/apb_if.sv"
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "sv/apb_transfer.sv"
`include "sv/apb_config.sv"
`include "sv/apb_monitor.sv"
`include "sv/apb_collector.sv"
`include "sv/apb_master_driver.sv"
`include "sv/apb_master_sequencer.sv"
`include "sv/apb_master_agent.sv"

class agent_test extends uvm_test;

  apb_master_agent agent;

  `uvm_component_utils(agent_test)

  function new(string name="agent_test", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    agent = apb_master_agent::type_id::create("agent", this);
  endfunction : build_phase

  function void start_of_simulation_phase(uvm_phase phase);
    this.print();
    uvm_test_done.set_drain_time(this, 100);
  endfunction : start_of_simulation_phase
endclass : agent_test

bit clk, reset;

apb_if apb_if0 (clk, reset);

initial begin
  uvm_config_db#(virtual apb_if)::set(null, "*", "vif", apb_if0);
  run_test("agent_test");
end

endmodule : test
