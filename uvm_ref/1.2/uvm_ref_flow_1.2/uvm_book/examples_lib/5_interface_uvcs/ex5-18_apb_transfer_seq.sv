/*******************************************************************************
  Example 5-18: APB Simple Sequence

  To run:  %  irun -uvm ex5-18_apb_transfer_seq.sv

  OR:      %  irun -uvmhome $UVM_HOME ex5-18_apb_transfer_seq.sv
*******************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"

//-----------------------------------------------------------------------------
// SEQUENCE: apb_transfer_seq
//-----------------------------------------------------------------------------
class apb_transfer_seq extends uvm_sequence #(apb_transfer);

  function new(string name="apb_transfer_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(apb_transfer_seq)

  // A simple sequence to execute a single random APB transfer
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    // Execute an APB transfer
    `uvm_do(req)

    // NOTE:  The above macro expands to the following:
    //    req = apb_transfer::type_id::create("req");
    //    start_item(req);
    //    if(!req.randomize())
    //      `uvm_warning("RNDFLD", "Randomization failed")
    //    finish_item(req);
  endtask
endclass : apb_transfer_seq
