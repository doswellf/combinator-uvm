/****************************************************************
  Example 7-14: UART Controller Virtual Sequence

  No testcase for this example.  Please run the full example
****************************************************************/

class u2a_a2u_vseq extends base_vseq;

  function new(string name="u2a_a2u_vseq");
      super.new(name);
  endfunction : new

 `uvm_object_utils(u2a_a2u_vseq)

  // APB sequences
  apb_config_seq config_seq;
  apb_a2u_seq a2u_seq;

  // UART sequences
  uart_u2a_seq u2a_seq;

  virtual task body();
    `uvm_info("U2A_A2U_VSEQ", "Executing", UVM_LOW)
    // Configure UART Controller DUT via the APB sequencer
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)
    // Then execute the u2a and a2u sequences in parallel
    fork
      `uvm_do_on(u2a_seq, p_sequencer.uart_seqr)
      `uvm_do_on(a2u_seq, p_sequencer.apb_seqr)
    join
  endtask : body
endclass : u2a_a2u_vseq
