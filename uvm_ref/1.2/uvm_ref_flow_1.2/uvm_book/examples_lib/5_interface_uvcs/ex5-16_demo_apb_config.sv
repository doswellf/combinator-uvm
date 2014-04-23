/****************************************************************
  Example 5-16: Extending the Default APB Configuration

  To run:   %  irun -uvm ex5-16_demo_apb_config.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-16_demo_apb_config.sv
****************************************************************/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "sv/apb_config.sv"

class demo_config extends apb_config;
  `uvm_object_utils(demo_config)

  function new(string name = "demo_config");
    super.new(name);
    add_slave("slave0", 32'h0000_0000, 32'h7FFF_FFFF, 0, UVM_ACTIVE);
    add_slave("slave1", 32'h8000_0000, 32'hFFFF_FFFF, 1, UVM_PASSIVE);
    add_master("master", UVM_ACTIVE);
  endfunction

endclass : demo_config

demo_config apb_cfg;

initial begin
  apb_cfg = demo_config::type_id::create("apb_cfg", null);
  apb_cfg.print();
end

endmodule : test
