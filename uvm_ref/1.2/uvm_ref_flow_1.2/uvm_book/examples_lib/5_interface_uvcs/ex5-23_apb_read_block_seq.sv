/*******************************************************************************
  Example 5-23: APB Sequence Incorporating End of Test

  To run:  %  irun -uvm ex5-23_apb_read_block_seq.sv

  OR:      %  irun -uvmhome $UVM_HOME ex5-23_apb_read_block_seq.sv
*******************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"

//------------------------------------------------------------------------------
// SEQUENCE: apb_read_block_seq
//------------------------------------------------------------------------------
class apb_read_block_seq extends uvm_sequence #(apb_transfer);

  rand bit [31:0] start_addr;
  rand int num_seq;
  constraint c_start_addr { start_addr[1:0] == 2'b00; }
  constraint c_num_seq { num_seq inside {[1:10]}; }

  // Constructor and UVM automation macros
  `uvm_object_utils(apb_read_block_seq)
  function new(string name="apb_read_block_seq");
    super.new(name);
  endfunction

  virtual task pre_body();
    // Raise end-of phase objection
    if (starting_phase != null)
      starting_phase.raise_objection(this, "APB read block");
  endtask

  virtual task body();
    // read block activity
    repeat(num_seq) begin
      `uvm_do_with(req, {req.addr == start_addr;} )
      start_addr = start_addr+4;
    end
  endtask

  virtual task post_body();
     // Drop end-of-phase objection if started as a root sequence
     if (starting_phase != null)
        starting_phase.drop_objection(this, "APB read block");
  endtask
endclass : apb_read_block_seq
