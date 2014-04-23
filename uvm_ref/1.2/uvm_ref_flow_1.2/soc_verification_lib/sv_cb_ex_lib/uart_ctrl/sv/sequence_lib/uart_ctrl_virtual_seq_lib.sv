/*-------------------------------------------------------------------------
File name   : uart_ctrl_virtual_seq_lib.sv
Title       : Virtual Sequence
Project     :
Created     :
Description : This file implements the virtual sequence for the APB-UART env.
Notes       : The concurrent_u2a_a2u_rand_trans_vseq sequence first configures
            : the UART RTL. Once the configuration sequence is completed
            : random read/write sequences from both the UVCs are enabled
            : in parallel. At the end a Rx FIFO read sequence is executed.
            : The read_rx_fifo_seq needs to be modified to take interrupt into account.
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/


`ifndef UART_CTRL_VIRTUAL_SEQ_LIB_SV
`define UART_CTRL_VIRTUAL_SEQ_LIB_SV

class base_vseq extends uvm_sequence;
  function new(string name="base_vseq");
    super.new(name);
  endfunction

  `uvm_object_utils(base_vseq)
 `uvm_declare_p_sequencer(uart_ctrl_virtual_sequencer)

// Use a base sequence to raise/drop objections if this is a default sequence
  virtual task pre_body();
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence '",
                                              get_full_name(), "'"});
  endtask

  virtual task post_body();
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence '",
                                             get_full_name(), "'"});
  endtask
endclass : base_vseq

//-------------------------------------------------------------------
// SEQUENCE: concurrent u2a_a2u_rand_trans_vseq
//-------------------------------------------------------------------
class concurrent_u2a_a2u_rand_trans_vseq extends base_vseq;

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="concurrent_u2a_a2u_rand_trans_vseq");
    super.new(name);
  endfunction : new

 `uvm_object_utils(concurrent_u2a_a2u_rand_trans_vseq)

  constraint num_a2u_wr_ct {(num_a2u_wr <= 6);}
  constraint num_u2a_wr_ct {(num_u2a_wr <= 9);}

  //UART Controller Configuration Sequence
  uart_ctrl_config_reg_seq  config_seq;

  // APB sequences
  apb_to_uart_wr a2u_seq;
  read_rx_fifo_seq rd_rx_fifo;

  // UART sequences
  uart_transmit_seq u2a_seq;

  virtual task body();                      //lab4_note2
    `uvm_info("UART_VSEQ", "Executing", UVM_LOW)
    `uvm_info("UART_VSEQ", $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info("UART_VSEQ", $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info("UART_VSEQ", $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)  // Register Sequence

    fork
      // Write UART DUT TX FIFO from APB UVC and transmit data from UART UVC
      `uvm_do_on_with(a2u_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})
      `uvm_do_on_with(u2a_seq, p_sequencer.uart_seqr, {num_of_tx == num_u2a_wr;})
    join
    #10000;
    // Read UART DUT RX FIFO from APB UVC
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})
    `uvm_info("UART_VSEQ", "Completed", UVM_LOW)
  endtask : body
endclass : concurrent_u2a_a2u_rand_trans_vseq

//-------------------------------------------------------------------
// SEQUENCE: u2a_incr_payload_vseq
//-------------------------------------------------------------------
class u2a_incr_payload_vseq extends base_vseq;

  rand int unsigned num_u2a_wr;
  rand int unsigned num_a2u_wr;

  function new(string name="u2a_incr_payload_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_object_utils(u2a_incr_payload_vseq)

  constraint num_u2a_wr_ct {(num_u2a_wr > 2) && (num_u2a_wr <= 10);}
  constraint num_a2u_wr_ct {(num_a2u_wr == 0);}

  // APB and UART UVC sequences
  uart_incr_payload_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  //UART Controller Configuration Sequence
  uart_ctrl_config_reg_seq  config_seq;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // Configure the DUT with UVM_REG
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)  

    `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {cnt == num_u2a_wr;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

  endtask : body

endclass : u2a_incr_payload_vseq

class u2a_bad_parity_vseq extends base_vseq;

  rand int unsigned num_u2a_wr;
  rand int unsigned num_a2u_wr;

  function new(string name="u2a_bad_parity_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_object_utils(u2a_bad_parity_vseq)

  constraint num_u2a_wr_ct {(num_u2a_wr <= 10);}
  constraint num_a2u_wr_ct {(num_a2u_wr == 0);}

  //UART Controller Configuration Sequence
  uart_ctrl_config_reg_seq  config_seq;

  // APB and UART UVC sequences
  uart_bad_parity_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // Configure the DUT with UVM_REG
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)

    `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {cnt == num_u2a_wr;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

  endtask : body

endclass : u2a_bad_parity_vseq

class error_reg_vseq extends base_vseq;

  rand int unsigned num_u2a_wr;
  rand int unsigned num_a2u_wr;

  function new(string name="error_reg_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_object_utils(error_reg_vseq)

  constraint num_u2a_wr_ct {(num_u2a_wr <= 10);}
  constraint num_a2u_wr_ct {(num_a2u_wr == 0);}

  //UART Controller Configuration Sequence
  uart_ctrl_config_reg_seq  config_seq;

  // APB and UART UVC sequences
  uart_bad_parity_seq uart_seq;
  read_rx_fifo_then_error_reg_seq rd_rx_fifo;  

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // Configure the DUT with UVM_REG
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)

    `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {cnt == num_u2a_wr;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

  endtask : body

endclass : error_reg_vseq  

class uart_1_stopbit_rx_traffic_vseq extends base_vseq;

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="uart_1_stopbit_rx_traffic_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(uart_1_stopbit_rx_traffic_vseq)

  constraint num_a2u_wr_ct {(num_a2u_wr == 1);}
  constraint num_u2a_wr_ct {(num_u2a_wr == 0);}

  //UART Controller Configuration Sequence
  uart_ctrl_1stopbit_reg_seq  config_seq;

  // APB  sequences
  apb_to_uart_wr raw_seq;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // Configure the DUT with UVM_REG
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)

    `uvm_do_on_with(raw_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})

    #800000;

  endtask : body

endclass : uart_1_stopbit_rx_traffic_vseq

// sequence having UART UVC transmitting data and receiving data
class uart_rx_tx_fifo_coverage_vseq extends base_vseq;

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="uart_rx_tx_fifo_coverage_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_object_utils(uart_rx_tx_fifo_coverage_vseq)

  constraint num_a2u_wr_ct {(num_a2u_wr == 17);}
  constraint num_u2a_wr_ct {(num_u2a_wr == 16);}

  //UART Controller Configuration Sequence
  uart_ctrl_config_reg_seq  config_seq;

  // APB sequences
  apb_to_uart_wr raw_seq;

  // UART sequences
  uart_transmit_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();                      //lab4_note2
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // Configure the DUT with UVM_REG
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)

    fork
      // Write UART DUT TX FIFO from APB UVC and transmit data from UART UVC
      `uvm_do_on_with(raw_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {num_of_tx == num_u2a_wr;})
    join
    #10000;
    // Read UART DUT RX FIFO from APB UVC
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

  endtask : body

endclass : uart_rx_tx_fifo_coverage_vseq

`endif  // UART_CTRL_VIRTUAL_SEQ_LIB_SV
