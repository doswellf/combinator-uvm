/*-------------------------------------------------------------------------
File name   : u2a_incr_payld_bd_parity.sv
Title       : Test Case
Project     :
Created     :
Description : One test case for the APB-UART Environment
Notes       : The test creates a uart_ctrl_tb and sets the default
            : sequence for the sequencer as u2a_bad_parity
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

class uart_bad_parity_test extends uvm_test;

  uart_ctrl_tb uart_ctrl_tb0;

  `uvm_component_utils(uart_bad_parity_test)

  function new(input string name, input uvm_component parent);
      super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    set_config_int("uart_ctrl_tb0.uart0.Tx.monitor", "checks_enable", 0);
    //set_config_string("uart_ctrl_tb0.virtual_sequencer", "default_sequence", "u2a_bad_parity_vseq");
    uvm_config_db#(uvm_object_wrapper)::set(this, "uart_ctrl_tb0.virtual_sequencer.run_phase",
          "default_sequence", u2a_bad_parity_vseq::type_id::get());
    uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0",this);
  endfunction : build_phase

endclass
