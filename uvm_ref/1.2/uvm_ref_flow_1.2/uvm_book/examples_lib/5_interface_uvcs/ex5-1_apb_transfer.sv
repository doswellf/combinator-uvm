/****************************************************************
  Example 5-1: APB Transfer

  The APB Transfer class definition plus a simple test to create,
  randomize and print three transfers

  To run:   %  irun -uvm ex5-1_apb_transfer.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-1_apb_transfer.sv

****************************************************************/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
//------------------------------------------------------------------------------
// CLASS: apb_transfer
//------------------------------------------------------------------------------
typedef enum bit {APB_READ, APB_WRITE} apb_direction_enum;

class apb_transfer extends uvm_sequence_item;                                  

  rand bit [31:0]           addr;
  rand bit [31:0]           data;
  rand apb_direction_enum   direction;
  // Control field - does not translate into signal data
  rand int unsigned         transmit_delay;
 
  constraint c_default_delay { transmit_delay inside {[0:100]} ; } 
  constraint c_default_addr { addr[1:0] == 2'b00; }

  `uvm_object_utils_begin(apb_transfer)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_enum(apb_direction_enum, direction, UVM_DEFAULT)
    `uvm_field_int(transmit_delay, UVM_DEFAULT|UVM_NOCOMPARE|UVM_NOPACK)
  `uvm_object_utils_end

  // Constructor - UVM sequence items require a string argument
  function new (string name = "apb_transfer");
    super.new(name);
  endfunction

endclass : apb_transfer


apb_transfer my_transfer;

initial begin
  my_transfer = new();
  repeat (3) begin
     void'(my_transfer.randomize());
     my_transfer.print();
  end
  $display("UVM DEFAULT TREE PRINTER FORMAT:");
  my_transfer.print(uvm_default_tree_printer);
  $display("UVM DEFAULT LINE PRINTER FORMAT:");
  my_transfer.print(uvm_default_line_printer);
end

endmodule : test
