/*******************************************************************************
 Example 5-22: UVM Sequence Library Usage

  To run:  %  irun -uvm ex5-22_sequence_library.sv

  OR:      %  irun -uvmhome $UVM_HOME ex5-22_sequence_library.sv
*******************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"
`include "sv/apb_transfer_seq.sv"
`include "sv/multi_apb_transfer_seq.sv"
`include "sv/apb_write_read_word_seq.sv"
`include "sv/apb_traffic_seq.sv"

//------------------------------------------------------------------------------
// SEQUENCE LIBRARY: mydut_seq_lib
//-------------------------------------------------------------------
class mydut_seq_lib extends uvm_sequence_library #(apb_transfer);

  `uvm_object_utils(mydut_seq_lib)
  `uvm_sequence_library_utils(mydut_seq_lib)

  function new(string name="mydut_seq_lib");
    super.new(name);
    // built-in fields
    min_random_count = 1;
    max_random_count = 5;
    // add sequences for this library
    add_sequence(apb_transfer_seq::get_type());
    add_sequence(multi_apb_transfer_seq::get_type());
    add_sequence(apb_write_read_word_seq::get_type());
    add_sequence(apb_traffic_seq::get_type());
    init_sequence_library();
  endfunction

endclass : mydut_seq_lib
