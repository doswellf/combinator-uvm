/****************************************************************
  Example 5-13: Configuring the APB UVC in the build() Method

  To run:   %  irun -uvmhome $UVM_HOME ex5-13_apb_env_build.sv
****************************************************************/
`include "sv/apb_if.sv"
`include "uvm_pkg.sv"
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
// Everything is defined in apb_env1.sv except the build function
`define BUILD_EX
`include "sv/apb_env1.sv"

// UVM build() phase
function void apb_env::build();
  uvm_object config_obj;
  super.build();

  // Get or create the APB UVC configuration class
  if(cfg == null)  begin
    `uvm_info(get_type_name(), "NOCONFIG: creating an apb_config", UVM_MEDIUM)
    cfg = apb_config::type_id::create("cfg");
    if (!cfg.randomize()) `uvm_fatal("RANDFAIL", "APB Config rand failed")
    cfg.print();
  end
  if (cfg.has_bus_monitor) begin
    bus_monitor = apb_bus_monitor::type_id::create("bus_monitor",this);
    bus_monitor.cfg = cfg;
  end
  master = apb_master_agent::type_id::create(cfg.master_config.name,this);
  master.cfg = cfg;
  slaves = new[cfg.slave_configs.size()];
  foreach(slaves[i]) begin
    slaves[i] = apb_slave_agent::type_id::create($sformatf("slave[%0d]", i), this);
    slaves[i].cfg = cfg.slave_configs[i];
  end
endfunction : build

// Simple testbench class
class demo_tb extends uvm_env;
  `uvm_component_utils(demo_tb)
  apb_env apb0;
  apb_config apb_cfg;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  virtual function void build();
    apb0 = apb_env::type_id::create("apb0", this);
  endfunction : build
  virtual function void connect();
    apb0.assign_vi(test.apb_if0);
  endfunction : connect
endclass : demo_tb

bit clk, reset;

apb_if apb_if0 (clk, reset);

demo_tb tb;

initial begin
  tb = demo_tb::type_id::create("tb", null);
  run_test();
end

initial
  #100 global_stop_request();

endmodule : test
