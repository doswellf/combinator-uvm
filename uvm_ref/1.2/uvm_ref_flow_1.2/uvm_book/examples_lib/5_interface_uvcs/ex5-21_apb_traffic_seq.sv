/*******************************************************************************
  Example 5-21: APB Traffic Sequence

  To run:  %  irun -uvm ex5-21_apb_traffic_seq.sv

  OR:      %  irun -uvmhome $UVM_HOME ex5-21_apb_traffic_seq.sv
*******************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"
`include "sv/apb_transfer_seq.sv"
`include "sv/multi_apb_transfer_seq.sv"
`include "sv/apb_write_read_word_seq.sv"

//------------------------------------------------------------------------------
// SEQUENCE: apb_traffic_seq
//------------------------------------------------------------------------------
class apb_traffic_seq extends uvm_sequence #(apb_transfer);

  multi_apb_transfer_seq   multi_seq;   // rand param: num_seq
  apb_write_read_word_seq  wr_rd_seq;   // rand param: start_addr

  // Constructor and UVM automation macros
  `uvm_object_utils(apb_traffic_seq)

  function new(string name="apb_traffic_seq");
    super.new(name);
  endfunction

  // The body executes two pre-defined sequences with constraints
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    repeat (5)
      `uvm_do_with( wr_rd_seq, { start_addr inside {['h0000:'h1fff]}; } )
    `uvm_do_with( multi_seq, { num_seq == 5; } )
    repeat (5)
     `uvm_do_with(wr_rd_seq, { start_addr inside {['h2000:'hffff]};})
  endtask : body
endclass : apb_traffic_seq
