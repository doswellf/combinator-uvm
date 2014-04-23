/*******************************************************************************
  Example 5-25: APB Sequence Incorporating End of Test

  To run:  %  irun -uvm ex5-25_apb_read_byte_seq.sv

  OR:      %  irun -uvmhome $UVM_HOME ex5-25_apb_read_byte_seq.sv
*******************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"
`include "sv/apb_master_sequencer.sv"
`include "sv/apb_master_base_seq.sv"

//------------------------------------------------------------------------------
// SEQUENCE: apb_read_byte_seq
//------------------------------------------------------------------------------
class apb_read_byte_seq extends apb_master_base_seq;

  rand bit [31:0] start_addr;

  function new(string name="apb_read_byte_seq");
    super.new(name);
  endfunction

  // Constructor and UVM automation macros
  `uvm_object_utils(apb_read_byte_seq)

  virtual task body();
    `uvm_info(get_type_name(), "Starting ...", UVM_HIGH)
    `uvm_do_with(req, {req.addr == start_addr; req.direction == APB_READ; })
  endtask

endclass : apb_read_byte_seq
