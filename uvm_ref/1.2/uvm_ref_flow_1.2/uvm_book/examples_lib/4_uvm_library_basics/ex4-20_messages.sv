/****************************************************************
  Example 4-20: UVM Message Macros within Modules

  To run:   %  irun -uvm ex4-20_messages.sv
****************************************************************/
module test;
`include "uvm_macros.svh"
import uvm_pkg::*;

initial begin
   uvm_report_info("TEST", "I am in the top-level test", UVM_NONE);
   `uvm_info("TEST", "I am in the top-level test", UVM_NONE)
end

endmodule : test
