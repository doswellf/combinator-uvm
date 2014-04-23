/****************************************************************
  Example 4-2: APB Transfer Derived from uvm_object

  To run:   %  irun -uvm ex4-2_apb_transfer.sv
  OR:       %  irun -uvmhome $UVM_HOME ex4-2_apb_transfer.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
//------------------------------------------------------------------------------
// CLASS: apb_transfer
//------------------------------------------------------------------------------
typedef enum bit {APB_READ, APB_WRITE} apb_direction_enum;
class apb_transfer extends uvm_object;
  rand bit [31:0]           addr;
  rand bit [31:0]           data;
  rand apb_direction_enum   direction;
  // Control field - does not translate into signal data
  rand int unsigned         transmit_delay;
   
  // UVM automation macros for data items
  `uvm_object_utils_begin(apb_transfer)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_enum(apb_direction_enum, direction, UVM_DEFAULT)
    `uvm_field_int(transmit_delay, UVM_DEFAULT | UVM_NOCOMPARE)
  `uvm_object_utils_end

  // Constructor - required UVM syntax
  function new (string name = "apb_transfer");
    super.new(name);
  endfunction

endclass : apb_transfer

module test;

apb_transfer transfer;

initial begin
  transfer = new("transfer");
  repeat (3) begin
    void'(transfer.randomize());
    transfer.print();
  end
end

endmodule : test
