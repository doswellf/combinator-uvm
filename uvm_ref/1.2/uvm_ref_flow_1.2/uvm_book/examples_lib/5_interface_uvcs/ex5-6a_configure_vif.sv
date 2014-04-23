/****************************************************************
  Example 5-6a: Configuring the virtual interface

  To run:   %  irun -uvm ex5-6a_configure_vif.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-6a_configure_vif.sv
****************************************************************/
`include "sv/apb_if.sv"
`include "uvm_pkg.sv"
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

bit clk, resetn;

apb_if apb_if0 (clk, resetn);

initial begin
  // set the virtual interface for the apb0 before running the test
  uvm_config_db#(virtual apb_if)::set(null, "*apb0*", "vif", apb_if0);
//  run_test();
end

endmodule : test
