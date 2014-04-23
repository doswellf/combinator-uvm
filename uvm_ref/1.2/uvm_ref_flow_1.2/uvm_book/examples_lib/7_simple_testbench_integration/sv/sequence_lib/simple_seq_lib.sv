/*-------------------------------------------------------------------------
File name   : simple_seq_lib.sv
Title       : 
Project     :
Created     :
Description : This file implements APB Sequences specific to UART 
            : Programming the DUT and Rx FIFO read
Notes       : 
            : 
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

// configures UART DUT Registers 
class program_dut_seq extends uvm_sequence #(apb_pkg::apb_transfer);

    function new(string name="program_dut_seq");
      super.new(name);
    endfunction
  
    rand uart_pkg::uart_config cfg;

    // Register sequence with a sequencer 
    `uvm_sequence_utils(program_dut_seq, apb_pkg::apb_master_sequencer)    

    bit [31:0] start_addr;
    bit [31:0] write_data;
    rand int unsigned transmit_del = 0;
    constraint c_transmit_del { transmit_del <= 8; }

    virtual task body();
      `uvm_info(get_type_name(), "Starting...", UVM_LOW)
      response_queue_error_report_disabled = 1;

      start_addr = `LINE_CTRL;
      write_data = {1'b1, 5'b0 ,2'h3};
        `uvm_do_with(req, 
          { req.addr == start_addr;
            req.direction == APB_WRITE;
            req.data == write_data;
            req.transmit_delay == transmit_del; } )

      start_addr = `DIVD_LATCH1;
        `uvm_do_with(req, 
          { req.addr == start_addr;
            req.direction == APB_WRITE;
            req.transmit_delay == transmit_del; } )

      start_addr = `DIVD_LATCH2;
        `uvm_do_with(req, 
          { req.addr == start_addr;
            req.direction == APB_WRITE;
            req.transmit_delay == transmit_del; } )

      start_addr = `LINE_CTRL;
      write_data = {1'b0, 5'b0 ,2'h3};
        `uvm_do_with(req, 
          { req.addr == start_addr;
            req.direction == APB_WRITE;
            req.data == write_data;
            req.transmit_delay == transmit_del; } )
    endtask
  
endclass : program_dut_seq

// Reads UART RX FIFO
class read_rx_fifo_seq extends uvm_sequence #(apb_pkg::apb_transfer);
    function new(string name="read_rx_fifo_seq");
      super.new(name);
    endfunction

    // Register sequence with a sequencer 
    `uvm_sequence_utils(read_rx_fifo_seq, apb_pkg::apb_master_sequencer)    

    rand bit [31:0] read_addr;
    rand int unsigned transmit_del = 0;
    rand int unsigned num_of_rd;
    constraint num_of_rd_ct { (num_of_rd <= 150); }
    constraint transmit_del_ct { (transmit_del <= 10); }
    constraint addr_ct {(read_addr[1:0] == 0); }

    virtual task body();
      `uvm_info(get_type_name(), $sformatf("Starting %0d Reads...", num_of_rd), UVM_LOW)
      response_queue_error_report_disabled = 1;
      read_addr = `RX_FIFO_REG;      //rx fifo address
      for (int i = 0; i < num_of_rd; i++) begin
          `uvm_do_with(req, 
            { req.addr == read_addr;
              req.direction == APB_READ;
              req.transmit_delay == transmit_del; } )
      end
    endtask
  
endclass : read_rx_fifo_seq

//  UART Transmit sequence with delay
class uart_write_to_apb_seq extends uvm_sequence #(uart_frame);

  uart_transmit_seq uart_seq;

  // register sequence with a sequencer
  uvm_sequence_utils(uart_write_to_apb_seq, uart_sequencer)

   function new(string name="uart_tx_seq");
      super.new(name);
   endfunction

   virtual task body();
     `uvm_info(get_type_name(), "Executing...", UVM_LOW)
     #200
     `uvm_do_with(uart_seq, num_of_tx == 5;)
   endtask: body
endclass: uart_write_to_apb_seq
