/*-------------------------------------------------------------------------
File name   : uart_rx_tx_fifo_coverage.sv
Title       : Test Case
Project     :
Created     :
Description : One test case for the APB-UART Environment
Notes       : The test creates a uart_ctrl_tb and sets the default
            : sequence for the sequencer as uart_rx_tx_fifo_coverage
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

class uart_txrx_fifo_cov extends uvm_test;

  uart_ctrl_tb uart_ctrl_tb0;

  `uvm_component_utils(uart_txrx_fifo_cov)

  function new(input string name, input uvm_component parent=null);
      super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    uvm_config_db#(uvm_object_wrapper)::set(this, "uart_ctrl_tb0.virtual_sequencer.run_phase",
          "default_sequence", uart_rx_tx_fifo_coverage_vseq::type_id::get());
    super.build_phase(phase);
    uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0",this);
  endfunction : build_phase

endclass
