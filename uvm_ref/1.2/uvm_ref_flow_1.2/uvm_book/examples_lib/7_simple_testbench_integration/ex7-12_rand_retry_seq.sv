/****************************************************************
  Example 7-12: UART Nested Retry Sequence

  To run:  %  irun -uvm -incdir ./uart/sv ./uart/sv/uart_pkg.sv \
                   ex7-12_rand_retry_seq.sv
****************************************************************/
`include "uart_if.sv"
import uvm_pkg::*;
`include "uvm_macros.svh"
import uart_pkg::*;
//------------------------------------------------------------------
// SEQUENCE: retry_seq - Send one BAD_PARITY frame followed by a
//                      GOOD_PARITY frame with the same payload
//------------------------------------------------------------------
class uart_retry_seq extends uvm_sequence #(uart_frame);
    rand bit [7:0] pload;

   // UVM automation for sequences
   `uvm_object_utils(uart_retry_seq)
   `uvm_declare_p_sequencer(uart_sequencer)

    function new(string name="uart_retry_seq");
      super.new(name);
    endfunction

    virtual task body();
      if (starting_phase != null)
        starting_phase.raise_objection(this, "Running sequence");
      `uvm_info("RETRY_SEQ", "Executing.", UVM_LOW)
      // Send the packet with parity constrained to BAD_PARITY
      `uvm_do_with(req, { payload == pload;
                          parity_type == uart_pkg::BAD_PARITY;})
      // Now send the packet with GOOD_PARITY
      `uvm_do_with(req, { payload == pload;
                          parity_type == uart_pkg::GOOD_PARITY;})
      if (starting_phase != null)
        starting_phase.drop_objection(this, "Completed sequence");
    endtask : body
endclass : uart_retry_seq
//----------------------------------------------------------------------
// SEQUENCE: rand_retry_seq - call retry_seq wrapped with random frames
//                      GOOD_PARITY frame with the same payload
//----------------------------------------------------------------------
class rand_retry_seq extends uvm_sequence #(uart_frame);

  // UVM automation 
  `uvm_object_utils(rand_retry_seq)

  // Constructor
  function new(string name="rand_retry_seq");
    super.new(name);
  endfunction


  uart_retry_seq retry_seq;  // A previously declared sequence

  virtual task body();
    if (starting_phase != null)
      starting_phase.raise_objection(this, "Running sequence");
    `uvm_info("RAND_RETRY_SEQ", "Executing.", UVM_LOW)
     // Send a random frame
     `uvm_do(req)
     // Execute the retry sequence with a constraint on pload
     `uvm_do_with(retry_seq, { pload inside {[0:31]};})
     // Send another random frame
     `uvm_do(req)
    if (starting_phase != null)
      starting_phase.drop_objection(this, "Completed sequence");
  endtask 

endclass : rand_retry_seq
