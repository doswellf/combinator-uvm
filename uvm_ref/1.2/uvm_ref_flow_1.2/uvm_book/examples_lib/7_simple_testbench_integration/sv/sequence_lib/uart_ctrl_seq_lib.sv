/*-------------------------------------------------------------------------
File name   : uart_ctrl_seq_lib.sv
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

class apb_to_uart_rd_after_wr extends uvm_sequence #(apb_pkg::apb_transfer);

    function new(string name="apb_to_uart_rd_after_wr");
      super.new(name);
    endfunction

    // Register sequence with a sequencer 
    `uvm_sequence_utils(apb_to_uart_rd_after_wr, apb_pkg::apb_master_sequencer)    

    rand bit [31:0] start_addr;
    rand int unsigned transmit_del = 0;
    constraint transmit_del_ct { (transmit_del <= 10); }
    constraint addr_ct {(start_addr[1:0] == 0); }

    virtual task body();
      `uvm_info(get_type_name(), "APB RGM Sequencer Starting...", UVM_LOW)
      response_queue_error_report_disabled = 1;
      start_addr = `TX_FIFO_REG;
        `uvm_do_with(req, 
          { req.addr == start_addr;
            req.direction == APB_WRITE;
            req.transmit_delay == transmit_del; } )

      start_addr = `TX_FIFO_REG;
        `uvm_do_with(req, 
          { req.addr == start_addr;
            req.direction == APB_READ;
            req.transmit_delay == transmit_del; } )
    endtask
  
endclass : apb_to_uart_rd_after_wr

// writes 0-150 data in UART TX FIFO
class apb_to_uart_wr extends uvm_sequence #(apb_pkg::apb_transfer);

    function new(string name="apb_to_uart_wr");
      super.new(name);
    endfunction

    // Register sequence with a sequencer 
    `uvm_sequence_utils(apb_to_uart_wr, apb_rgm_master_sequencer)    

    rand bit [31:0] start_addr;
    rand int unsigned transmit_del = 0;
    rand int unsigned num_of_wr;
    constraint num_of_wr_ct { (num_of_wr <= 150); }
    constraint transmit_del_ct { (transmit_del <= 10); }
    constraint addr_ct {(start_addr[1:0] == 0); }

    virtual task body();
      response_queue_error_report_disabled = 1;
      start_addr = `TX_FIFO_REG;
      while (num_of_wr) begin
        `uvm_info(get_type_name(), $sformatf("APB RGM Sequencer Starting %0d Writes...", num_of_wr), UVM_LOW)
        for (int i = 0; i < num_of_wr; i++) begin
          if (p_sequencer.tful) begin
            num_of_wr -= i;
            `uvm_info("UART_APB_SEQLIB", $sformatf("Breaking from apb_to_uart_wr since tfifo is not empty yet, pending num_of_wr = %d", num_of_wr), UVM_LOW)
            #10000;
            break;
          end
          `uvm_do_with(req, 
            { req.addr == start_addr;
              req.direction == APB_WRITE;
              req.transmit_delay == transmit_del; } )
          #200;
          if (i == num_of_wr - 1)
             num_of_wr = 0;
        end
      end
    endtask
  
endclass : apb_to_uart_wr


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
      `uvm_info(get_type_name(), $sformatf("APB RGM Sequencer Starting %0d Reads...", num_of_rd), UVM_LOW)
      response_queue_error_report_disabled = 1;

      for (int i = 0; i < num_of_rd; i++) begin
        read_addr = `RX_FIFO_REG;      //rx fifo address
          `uvm_do_with(req, 
            { req.addr == read_addr;
              req.direction == APB_READ;
              req.transmit_delay == transmit_del; } )
      end
    endtask
  
endclass : read_rx_fifo_seq

class apb_interrupt_from_uart extends uvm_sequence #(apb_pkg::apb_transfer);
//class apb_interrupt_from_uart extends apb_interrupt_seq;
   // register sequence with a sequencer 
  `uvm_sequence_utils(apb_interrupt_from_uart, apb_rgm_master_sequencer)

  function new(string name="apb_interrupt_from_uart");
    super.new(name);
  endfunction

    rand bit [31:0] read_addr;

/*
  virtual task body();
      `uvm_info(get_type_name(), "APB RGM Sequencer Starting...", UVM_LOW)
      response_queue_error_report_disabled = 1;
    forever begin
      @p_sequencer.vif.ua_int;
      grab(p_sequencer);
      `uvm_info("UART_APB_SEQLIB", $sformatf("Doing apb_interrupt_from_uart sequence"), UVM_LOW)
        read_addr = `CISR_REG;         //channel status register
        `uvm_do_with(req, 
            { req.addr == read_addr;
              req.direction == APB_READ;} )
      `uvm_info("UART_APB_SEQLIB", $sformatf("CISR_REG value is %h", req.data), UVM_LOW)
      if (req.data[0])
        `uvm_info("UART_APB_SEQLIB", $sformatf("rtrig interrupt is encountered  - no support yet"), UVM_LOW)
      if (req.data[1]) begin
        p_sequencer.rful = 0;
        `uvm_info("UART_APB_SEQLIB", $sformatf("rempty interrupt is encountered - stop reading from RX fifo"), UVM_LOW)
      end
      if (req.data[2]) begin
        p_sequencer.rful = 1;
        `uvm_info("UART_APB_SEQLIB", $sformatf("rful interrupt is encountered   - start reading from RX fifo"), UVM_LOW)
      end
      if (req.data[3]) begin
        p_sequencer.tful = 0;
        `uvm_info("UART_APB_SEQLIB", $sformatf("tempty interrupt is encountered - start sending transactions to TX fifo"), UVM_LOW)
      end
      if (req.data[4]) begin
        p_sequencer.tful = 1;
        `uvm_info("UART_APB_SEQLIB", $sformatf("tful interrupt is encountered   - stop sending transactions to TX fifo"), UVM_LOW)
      end
      ungrab(p_sequencer);
    end
  endtask : body
*/
endclass : apb_interrupt_from_uart
  
