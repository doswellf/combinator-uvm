/*-------------------------------------------------------------------------
File name   : uart_ctrl_interrupt_seq_lib.sv
Title       : 
Project     :
Created     :
Description : This file implements APB Sequences specific to UART 
            : CSR programming and Tx/Rx FIFO write/read
Notes       : The interrupt sequence in this file is not yet complete.
            : The interrupt sequence should be triggred by the Rx fifo 
            : full event from the UART RTL.
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/
//-------------------------------------------------------------------
// SEQUENCE: apb_interrupt_seq
//-------------------------------------------------------------------
class apb_interrupt_seq extends uvm_sequence #(apb_transfer);
  `uvm_object_utils(apb_interrupt_seq)
  `uvm_declare_p_sequencer(apb_master_sequencer)

  function new(string name="apb_interrupt_seq");
    super.new(name);
  endfunction

  virtual task body();
    forever begin
      @p_sequencer.vif.ua_int;
      grab(p_sequencer);
      `uvm_info("INTERRUPT_SEQ", "Doing INTERRUPT Sequence", UVM_LOW)
      ungrab(p_sequencer);
    end
  endtask : body

endclass : apb_interrupt_seq
  
//-------------------------------------------------------------------
// SEQUENCE: apb_interrupt_seq
//-------------------------------------------------------------------
class apb_interrupt_from_uart extends uvm_sequence #(apb_pkg::apb_transfer);
   // register sequence with a sequencer 
  `uvm_object_utils(apb_interrupt_from_uart)
  `uvm_declare_p_sequencer(apb_master_sequencer)
  //`uvm_declare_p_sequencer(apb_rgm_master_sequencer)  //KAM - remove

  function new(string name="apb_interrupt_from_uart");
    super.new(name);
  endfunction

    rand bit [31:0] read_addr;

  virtual task body();
      response_queue_error_report_disabled = 1;
    forever begin
      @p_sequencer.vif.ua_int;
      grab(p_sequencer);
      `uvm_info("UART_INTERRUPT_SEQ", "Executing apb_interrupt_from_uart sequence", UVM_LOW)
        read_addr = `CISR_REG;         //channel status register
        `uvm_do_with(req, 
            { req.addr == read_addr;
              req.direction == APB_READ;} )
      `uvm_info("UART_INTERRUPT_SEQ", $sformatf("CISR_REG value is %h", req.data), UVM_LOW)
      if (req.data[0])
        `uvm_info("UART_INTERRUPT_SEQ", "Interrupt: rtrig - No support yet", UVM_LOW)
      if (req.data[1]) begin
        p_sequencer.rful = 0;
        `uvm_info("UART_INTERRUPT_SEQ", "Interrupt: rempty - Stop reading from RX fifo", UVM_LOW)
      end
      if (req.data[2]) begin
        p_sequencer.rful = 1;
        `uvm_info("UART_INTERRUPT_SEQ", "Interrupt: rful - Start reading from RX fifo", UVM_LOW)
      end
      if (req.data[3]) begin
        p_sequencer.tful = 0;
        `uvm_info("UART_INTERRUPT_SEQ", "Interrupt: tempty - Start sending transactions to TX fifo", UVM_LOW)
      end
      if (req.data[4]) begin
        p_sequencer.tful = 1;
        `uvm_info("UART_INTERRUPT_SEQ", "Interrupt: tful - Stop sending transactions to TX fifo", UVM_LOW)
      end
      ungrab(p_sequencer);
    end
  endtask : body
endclass : apb_interrupt_from_uart
