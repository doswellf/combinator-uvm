/**********************************************************************
  Example 10-9: Module UVC DUT Coverage

  Kit Location : $UVM_REF_HOME/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/coverage/uart_ctrl_cover.sv
*********************************************************************/
/*-------------------------------------------------------------------------
File name   : uart_cover.sv
Title       : APB<>UART coverage collection
Project     :
Created     :
Description : Collects coverage around the UART DUT
            : 
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

class uart_ctrl_cover extends  uvm_component ;

  virtual interface uart_ctrl_if vif;

  bit coverage_enable = 1;

  int unsigned mod_tx_fifo_ptr
  int unsigned mod_rx_fifo_ptr;

  // Required macro for UVM automation and utilities
  `uvm_component_utils(uart_ctrl_cover)

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (!uvm_config_db#(virtual uart_ctrl_if)::get(this, get_full_name(),"vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
    fork
      collect_tx_coverage();
      collect_rx_coverage();
    join

  endtask : run_phase

  virtual task collect_tx_coverage();
    // Calculate percentage fill level of TX FIFO
    forever begin
      @(vif.tx_fifo_ptr)
        mod_tx_fifo_ptr = (vif.tx_fifo_ptr*100/`UA_TX_FIFO_DEPTH);
        if (coverage_enable) dut_tx_fifo_cg.sample();
    end  
  endtask : collect_tx_coverage

  virtual task collect_rx_coverage();
    // Calculate percentage fill level of RX FIFO
    forever begin
      @(vif.rx_fifo_ptr)
        mod_rx_fifo_ptr = (vif.rx_fifo_ptr*100/`UA_RX_FIFO_DEPTH);
        if (coverage_enable) dut_rx_fifo_cg.sample();
    end  
  endtask : collect_rx_coverage

  // --------------------------------
  // Covergroup definitions
  // --------------------------------

  // DUT TX FIFO covergroup
  covergroup dut_tx_fifo_cg;
    tx_level              : coverpoint mod_tx_fifo_ptr {
                             bins EMPTY = {0};
                             bins HALF_FULL = {[50:99]};
                             bins FULL = {100};
                            }
  endgroup


  // DUT RX FIFO covergroup
  covergroup dut_rx_fifo_cg;
    rx_level              : coverpoint mod_rx_fifo_ptr {
                             bins EMPTY = {0};
                             bins HALF_FULL = {[40:99]};
                             bins FULL = {100};
                            }
  endgroup

  function new(string name , uvm_component parent);
    super.new(name, parent);
    dut_rx_fifo_cg = new();
    dut_rx_fifo_cg.set_inst_name ("dut_rx_fifo_cg");

    dut_tx_fifo_cg = new();
    dut_tx_fifo_cg.set_inst_name ("dut_tx_fifo_cg");

  endfunction
  
endclass : uart_ctrl_cover
