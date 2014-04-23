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

  virtual interface uart_ctrl_internal_if vif;
  uart_pkg::uart_config uart_cfg;

  event tx_fifo_ptr_change;
  event rx_fifo_ptr_change;


  // Required macro for UVM automation and utilities
  `uvm_component_utils(uart_ctrl_cover)

  virtual task run_phase(uvm_phase phase);
    fork
      collect_tx_coverage();
      collect_rx_coverage();
    join

  endtask : run_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (!uvm_config_db#(virtual uart_ctrl_internal_if)::get(this, get_full_name(),"vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
  endfunction : connect_phase

  virtual task collect_tx_coverage();
    // --------------------------------
    // Extract & re-arrange to give a more useful input to covergroups
    // --------------------------------
    // Calculate percentage fill level of TX FIFO
    forever begin
      @(vif.tx_fifo_ptr)
    //do any processing here
      -> tx_fifo_ptr_change;
    end  
  endtask : collect_tx_coverage

  virtual task collect_rx_coverage();
    // --------------------------------
    // Extract & re-arrange to give a more useful input to covergroups
    // --------------------------------
    // Calculate percentage fill level of RX FIFO
    forever begin
      @(vif.rx_fifo_ptr)
    //do any processing here
      -> rx_fifo_ptr_change;
    end  
  endtask : collect_rx_coverage

  // --------------------------------
  // Covergroup definitions
  // --------------------------------

  // DUT TX FIFO covergroup
  covergroup dut_tx_fifo_cg @(tx_fifo_ptr_change);
    tx_level              : coverpoint vif.tx_fifo_ptr {
                             bins EMPTY = {0};
                             bins HALF_FULL = {[7:10]};
                             bins FULL = {[13:15]};
                            }
  endgroup


  // DUT RX FIFO covergroup
  covergroup dut_rx_fifo_cg @(rx_fifo_ptr_change);
    rx_level              : coverpoint vif.rx_fifo_ptr {
                             bins EMPTY = {0};
                             bins HALF_FULL = {[7:10]};
                             bins FULL = {[13:15]};
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
