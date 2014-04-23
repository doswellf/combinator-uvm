/**********************************************************************
  Example 10-8: UART Controller Virtual Sequence

  %  irun -uvm ex10-8_uart_ctrl_virtual_seq.sv
 
  This code came from:
  Kit Location : $UVM_REF_HOME/soc_verification_libs/sv_cb_ex_lib/uart_ctrl/sv/sequence_lib/uart_ctrl_virtual-seq_lib.sv
*********************************************************************/

//`include "ex10-7_uart_ctrl_base_vseq.sv"

// sequence having UART UVC transmitting data and receiving data
class concurrent_u2a_a2u_rand_trans_vseq extends base_vseq;

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="concurrent_u2a_a2u_rand_trans_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_object_utils(concurrent_u2a_a2u_rand_trans_vseq)

  constraint num_a2u_wr_ct {(num_a2u_wr <= 20);}
  constraint num_u2a_wr_ct {(num_u2a_wr <= 10);}

  //UART Controller Configuration Sequence
  uart_ctrl_config_reg_seq  config_seq;

  // APB sequences
  apb_to_uart_wr a2u_seq;
  read_rx_fifo_seq rd_rx_fifo;

  // UART sequences
  uart_transmit_seq u2a_seq;

  virtual task body(); 
    `uvm_info("UART_VSEQ", "Executing", UVM_LOW)
    `uvm_info("UART_VSEQ", $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info("UART_VSEQ", $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info("UART_VSEQ", $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)   // Register Sequence

    fork
      // Write UART DUT TX FIFO from APB UVC and transmit data from UART UVC
      `uvm_do_on_with(a2u_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})
      `uvm_do_on_with(u2a_seq, p_sequencer.uart_seqr, {num_of_tx == num_u2a_wr;})
    join
    #10000;
    // Read UART DUT RX FIFO from APB UVC
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

  endtask : body
endclass : concurrent_u2a_a2u_rand_trans_vseq
