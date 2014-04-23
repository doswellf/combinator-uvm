/*******************************************************************************
  Example 5-19: APB Multiple Transfer Sequence

  To run:  %  irun -uvm ex5-19_multi_transfer_seq.sv

  OR:      %  irun -uvmhome $UVM_HOME ex5-19_multi_transfer_seq.sv
*******************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"
`include "sv/apb_transfer_seq.sv"

//------------------------------------------------------------------------------
// SEQUENCE: multi_apb_transfer_seq
//------------------------------------------------------------------------------
class multi_apb_transfer_seq extends uvm_sequence #(apb_transfer);

  rand int num_seq;
  constraint c_num_seq { num_seq inside {[1:10]}; }

  // Constructor and UVM automation macros
  `uvm_object_utils(multi_apb_transfer_seq)
  function new(string name="multi_apb_transfer_seq");
    super.new(name);
  endfunction

  virtual task body();
     apb_transfer_seq apb_seq;  // Instance of another sequence type
     // Raise end-of phase objection
     if (starting_phase != null)
        starting_phase.raise_objection(this, "Starting multi_apb_transfer_seq");

    // Execute a apb transfer
    repeat(num_seq)
      `uvm_do(apb_seq)

     // Drop end-of-phase objection
     if (starting_phase != null)
        starting_phase.drop_objection(this, "Completed multi_apb_transfer_seq");
  endtask
endclass : multi_apb_transfer_seq
