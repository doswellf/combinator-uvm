/****************************************************************
  File: apb_transfer.sv
****************************************************************/
//----------------------------------------------------------------------------
// CLASS: apb_transfer
//----------------------------------------------------------------------------
typedef enum bit {APB_READ, APB_WRITE} apb_direction_enum;
class apb_transfer extends uvm_sequence_item;                                  

  rand bit [31:0]           addr;
  rand bit [31:0]           data;
  rand apb_direction_enum   direction;
  // Control field - does not translate into signal data
  rand int unsigned         transmit_delay;

  // Constraint
  constraint c_transmit_delay { transmit_delay inside {[0:15]}; }
   
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
