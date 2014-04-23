/****************************************************************
  Example 5-7: Non-UVM Generator Code

  To run:   %  irun -uvm ex5-7_generator.sv
****************************************************************/
module test();
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"

class generator;
  rand int max_count = 3;
  int count;
  apb_transfer transfer;

  task get_next_item(output apb_transfer trans);
    if (count <= max_count) begin
      transfer = apb_transfer::type_id::create("transfer");
      if (!transfer.randomize())
        `uvm_fatal("RANDFAIL", "Failure to randomize transfer")
      trans = transfer;
      count++;
    end
    else `uvm_warning("MAXCNT", "Maximum transfer count reached")
  endtask : get_next_item

endclass : generator

generator my_gen;
apb_transfer trans;

initial begin
   my_gen = new();
   repeat (4) begin
     my_gen.get_next_item(trans);
     if (trans != null) trans.print();
   end
end

endmodule :test
