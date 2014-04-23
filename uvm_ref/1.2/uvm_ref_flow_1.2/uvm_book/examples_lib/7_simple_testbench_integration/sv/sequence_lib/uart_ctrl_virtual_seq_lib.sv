/*-------------------------------------------------------------------------
File name   : uart_ctrl_virtual_seq_lib.sv
Title       : Virtual Sequence
Project     :
Created     :
Description : This file implements the virtual sequence for the APB-UART env.
Notes       : The concurrent_u2a_a2u_rand_trans sequence first configures
            : the UART RTL. Once the configuration sequence is completed
            : random read/write sequences from both the UVCs are enabled
            : in parallel. At the end a Rx FIFO read sequence is executed.
            : The read_rx_fifo_seq needs to be modified to take interrupt into account.
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/


`ifndef UART_CTRL_VIRTUAL_SEQ_LIB_SV
`define UART_CTRL_VIRTUAL_SEQ_LIB_SV

// sequence having UART UVC transmitting data and receiving data
class concurrent_u2a_a2u_rand_trans_vseq extends uvm_sequence;

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="concurrent_u2a_a2u_rand_trans_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_sequence_utils(concurrent_u2a_a2u_rand_trans_vseq, uart_ctrl_virtual_sequencer)    //lab4_note1

  constraint num_a2u_wr_ct {(num_a2u_wr <= 6);}
  constraint num_u2a_wr_ct {(num_u2a_wr <= 9);}

  // APB sequences
  uart_cfg_rgm_seq uart_cfg_dut_seq;    // CONFIGURE DUT
  apb_to_uart_wr raw_seq;
  // UART sequences
  uart_transmit_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();                      //lab4_note2
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    fork
      // Write UART DUT TX FIFO from APB UVC and transmit data from UART UVC
      `uvm_do_on_with(raw_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {num_of_tx == num_u2a_wr;})
    join
    #10000;
    // Read UART DUT RX FIFO from APB UVC
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : concurrent_u2a_a2u_rand_trans_vseq

class u2a_incr_payload_vseq extends uvm_sequence;

  rand int unsigned num_u2a_wr;
  rand int unsigned num_a2u_wr;

  function new(string name="u2a_incr_payload_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_sequence_utils(u2a_incr_payload_vseq, uart_ctrl_virtual_sequencer)    

  constraint num_u2a_wr_ct {(num_u2a_wr > 2) && (num_u2a_wr <= 10);}
  constraint num_a2u_wr_ct {(num_a2u_wr == 0);}

  // APB and UART UVC sequences
  uart_cfg_rgm_seq uart_cfg_dut_seq;
  uart_incr_payload_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {cnt == num_u2a_wr;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : u2a_incr_payload_vseq

class u2a_bad_parity_vseq extends uvm_sequence;

  rand int unsigned num_u2a_wr;
  rand int unsigned num_a2u_wr;

  function new(string name="u2a_bad_parity_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_sequence_utils(u2a_bad_parity_vseq, uart_ctrl_virtual_sequencer)    

  constraint num_u2a_wr_ct {(num_u2a_wr <= 10);}
  constraint num_a2u_wr_ct {(num_a2u_wr == 0);}

  // APB and UART UVC sequences
  uart_cfg_rgm_seq uart_cfg_dut_seq;
  uart_bad_parity_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {cnt == num_u2a_wr;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : u2a_bad_parity_vseq

class uart_1_stopbit_rx_traffic_vseq extends uvm_sequence;

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="uart_1_stopbit_rx_traffic_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_sequence_utils(uart_1_stopbit_rx_traffic_vseq, uart_ctrl_virtual_sequencer)    

  constraint num_a2u_wr_ct {(num_a2u_wr <= 10);}
  constraint num_u2a_wr_ct {(num_u2a_wr == 0);}

  // APB  sequences
  uart_cfg_1stopbit_rgm_seq uart_cfg_dut_seq;
  apb_to_uart_wr raw_seq;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    `uvm_do_on_with(raw_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : uart_1_stopbit_rx_traffic_vseq

/*
class uart_remote_loopback_vseq extends uvm_sequence;

  rand int unsigned num_u2a_wr;

  function new(string name="uart_remote_loopback_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_sequence_utils(uart_remote_loopback_vseq, uart_ctrl_virtual_sequencer)    

  constraint num_u2a_wr_ct {(num_u2a_wr > 2) && (num_u2a_wr <= 10);}

  // APB and UART UVC sequences
  uart_cfg_remote_lpbk_rgm_seq uart_cfg_dut_seq;
  uart_incr_payload_vseq uart_seq;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %d", num_u2a_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {cnt == num_u2a_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : uart_remote_loopback_vseq

// Local Loopback
class uart_local_loopback_vseq extends uvm_sequence;

// class uart_local_cfg extends uart_pkg::uart_config;
//   constraint c_ua_chmode     { ua_chmode == 2'b10;} // set local feedback
//   constraint c_intrpt_en      { ua_ier     == 11'h004;}            //enable rx full interupts.
//   constraint c_intrpt_dis     { ua_idr     == 11'h7f1;}
//   `uvm_object_utils(uart_local_cfg)  
//  endclass: uart_local_cfg

  rand int unsigned num_a2u_wr;

  function new(string name="uart_local_loopback_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
 `uvm_sequence_utils(uart_local_loopback_vseq, uart_ctrl_virtual_sequencer)    

  constraint num_a2u_wr_ct {(num_a2u_wr == 2 );}

  // APB and UART UVC sequences
  uart_cfg_local_lpbk_rgm_seq uart_cfg_dut_seq;
  apb_to_uart_wr raw_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %d", num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    `uvm_do_on_with(raw_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_a2u_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : uart_local_loopback_vseq
*/

class uart_rx_tx_fifo_coverage_vseq extends uvm_sequence;

// class uart_rx_tx_fifodepth_8 extends uart_pkg::uart_config;
//   constraint c_intrpt_en      { ua_ier     == 11'h01e;}            //enable tx/rx full/empty interupts.
//   constraint c_intrpt_dis     { ua_idr     == 11'h7e1;}
//   `uvm_object_utils(uart_rx_tx_fifodepth_8)  
// endclass : uart_rx_tx_fifodepth_8

  rand int unsigned num_a2u_wr;
  rand int unsigned num_u2a_wr;

  function new(string name="uart_rx_tx_fifo_coverage_vseq");
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_sequence_utils(uart_rx_tx_fifo_coverage_vseq, uart_ctrl_virtual_sequencer)    

  constraint num_a2u_wr_ct {(num_a2u_wr == `UA_TX_FIFO_DEPTH + 5);}
  constraint num_u2a_wr_ct {(num_u2a_wr == `UA_TX_FIFO_DEPTH + 5);}

  // APB and UART UVC sequences
  uart_cfg_rxtx_fifo_cov_rgm_seq uart_cfg_dut_seq;
  apb_to_uart_wr raw_seq;
  uart_transmit_seq uart_seq;
  read_rx_fifo_seq rd_rx_fifo;

  virtual task body();
    `uvm_info(get_type_name(), "UART Controller Virtual Sequencer Executing", UVM_LOW)
    uvm_test_done.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Number of APB->UART Transaction = %0d", num_a2u_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Number of UART->APB Transaction = %0d", num_u2a_wr), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("Total Number of APB<->UART Transaction = %0d", num_u2a_wr + num_a2u_wr), UVM_LOW)

    // configure UART DUT
    `uvm_do_on(uart_cfg_dut_seq, p_sequencer.rgm_seqr)

    fork
      `uvm_do_on_with(raw_seq, p_sequencer.apb_seqr, {num_of_wr == num_a2u_wr;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart_seqr, {num_of_tx == num_u2a_wr;})
    join
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.apb_seqr, {num_of_rd == num_u2a_wr;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : uart_rx_tx_fifo_coverage_vseq

`endif  // UART_CTRL_VIRTUAL_SEQ_LIB_SV
