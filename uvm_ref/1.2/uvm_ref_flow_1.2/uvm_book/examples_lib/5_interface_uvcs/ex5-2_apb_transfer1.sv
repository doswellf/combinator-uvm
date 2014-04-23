
/****************************************************************
  Example 5-2: Defining a Transaction Control Field

  The APB Transfer Class with an additional control knob

  To run:   %  irun -uvm ex5-2_apb_transfer1.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-2_apb_transfer1.sv
****************************************************************/
module test();
import uvm_pkg::*;
`include "uvm_macros.svh"

//------------------------------------------------------------------------------
// CLASS: apb_transfer
//------------------------------------------------------------------------------
typedef enum bit {APB_READ, APB_WRITE} apb_direction_enum;
typedef enum {ZERO, SHORT, MEDIUM, LONG, MAX} apb_dly_enum;

class apb_transfer extends uvm_sequence_item;                                  

  rand bit [31:0]           addr;
  rand bit [31:0]           data;
  rand apb_direction_enum   direction;

  // Control fields - do not translate to signal data
  rand apb_dly_enum         delay_kind;
  rand int unsigned         transmit_delay;
 
  constraint c_addr { addr[1:0] == 2'b00; }
  constraint c_transmit_delay { solve delay_kind before transmit_delay;
           transmit_delay >= 0; transmit_delay <= 100 ; 
           (delay_kind == ZERO) -> transmit_delay == 0;
           (delay_kind == SHORT) -> transmit_delay inside {[1:10]}; 
           (delay_kind == MEDIUM) -> transmit_delay inside {[11:29]}; 
           (delay_kind == LONG) -> transmit_delay inside {[30:100]}; 
           (delay_kind == MAX) -> transmit_delay == 100;  }

  // UVM utilities and automation macros for data items
  `uvm_object_utils_begin(apb_transfer)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_enum(apb_direction_enum, direction, UVM_DEFAULT)
    `uvm_field_enum(apb_dly_enum, delay_kind, UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(transmit_delay, UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
  `uvm_object_utils_end

  // Constructor - required UVM syntax
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
  $display("my_transfer.randomize() with {delay_kind == MAX;} : ");
  void'(my_transfer.randomize() with {delay_kind == MAX;});
  my_transfer.print();
end



endmodule : test
