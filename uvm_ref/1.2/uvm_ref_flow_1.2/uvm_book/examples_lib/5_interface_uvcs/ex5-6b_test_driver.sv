/****************************************************************
  Example 5-6a: Simple APB Interface/Driver Test

  To run:   %  irun -uvm ex5-6a_test_driver.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-6a_test_driver.sv
****************************************************************/
`include "sv/apb_if.sv"
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

`include "sv/apb_transfer.sv"
`include "sv/apb_master_driver.sv"

bit clk, resetn;

apb_if apb_if0 (clk, resetn);

apb_master_driver driver;

initial begin
  // set the virtual interface for the apb0 before running the test
  //uvm_config_db#(virtual apb_if)::set(null, "*apb0*", "vif", apb_if0);
  uvm_config_db#(virtual apb_if)::set(null, "*", "vif", apb_if0);
  driver = apb_master_driver::type_id::create("driver", null);
  driver.vif = apb_if0;
end

endmodule : test
