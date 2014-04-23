/**********************************************************************
  Example 4-21: Message Callback Usage

  To run:   %  irun -uvm message_callback_test.sv
**********************************************************************/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

class verbosity_catcher extends uvm_report_catcher;
  virtual function action_e catch();
    case (get_verbosity())
      UVM_LOW, UVM_NONE, UVM_HIGH: return THROW;
      default : begin
                  issue();
                  return CAUGHT;
                end
    endcase
  endfunction 
endclass

verbosity_catcher catcher = new();

initial begin
  uvm_report_cb::add(null, catcher);
  `uvm_info("MYID", "UVM_LOW: This one should be printed", UVM_LOW);
  `uvm_info("MYID", "UVM_MEDIUM: This one should NOT be printed", UVM_MEDIUM);
  `uvm_info("MYID", "UVM_HIGH: This one should be printed", UVM_HIGH);
  `uvm_info("MYID", "UVM_HIGH+1: This one should NOT be printed", UVM_HIGH+1);
  `uvm_info("MYID", "UVM_FULL: This one should NOT be printed", UVM_FULL);
end
endmodule
