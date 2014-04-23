/****************************************************************
  Example 7-11: UART Retry Sequence

  To run:   %  irun -uvm -incdir ./uart/sv ./uart/sv/uart_pkg.sv \
               ex7-11_retry_seq.sv
****************************************************************/
`include "uart_if.sv"

import uvm_pkg::*;
`include "uvm_macros.svh"
import uart_pkg::*;
//------------------------------------------------------------------
// SEQUENCE: uart_retry_seq - Send one BAD_PARITY frame followed by
//                      a GOOD_PARITY frame with the same payload
//------------------------------------------------------------------
class uart_retry_seq extends uvm_sequence #(uart_frame);
  rand bit [7:0] pload;  // Randomizable sequence parameter

  // UVM automation for sequences
  `uvm_object_utils(uart_retry_seq)
  `uvm_declare_p_sequencer(uart_sequencer)

  // Constructor
  function new(string name="uart_retry_seq");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("RETRY_SEQ", {"Executing sequence: ", get_type_name()}, UVM_LOW)
    if (starting_phase != null)
      starting_phase.raise_objection(this, "Running sequence");
     // Send the packet with parity constrained to BAD_PARITY
    `uvm_do_with(req, { payload == pload; parity_type == uart_pkg::BAD_PARITY;})
     // Now send the packet with GOOD_PARITY
    `uvm_do_with(req, { payload == pload; parity_type == uart_pkg::GOOD_PARITY;})
    if (starting_phase != null)
      starting_phase.drop_objection(this, "Completed sequence");
    endtask : body

endclass : uart_retry_seq
