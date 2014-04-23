/*-------------------------------------------------------------------------
File name   : apb_subsystem_seq_lib.sv
Title       : 
Project     :
Created     :
Description : This file implements APB Sequences specific to UART 
            : CSR programming and Tx/Rx FIFO write/read
Notes       : The interrupt sequence in this file is not yet complete.
            : The interrupt sequence should be triggred by the Rx fifo 
            : full event from the UART RTL.
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

// writes 0-150 data in UART TX FIFO
class ahb_to_uart_wr extends uvm_sequence #(ahb_transfer);

    function new(string name="ahb_to_uart_wr");
      super.new(name);
    endfunction

    // Register sequence with a sequencer 
    `uvm_object_utils(ahb_to_uart_wr)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    rand bit unsigned[31:0] rand_data;
    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;
    bit [`AHB_ADDR_WIDTH-1:0] start_addr;
    rand bit [`AHB_DATA_WIDTH-1:0] write_data;
    rand int unsigned num_of_wr;
    constraint num_of_wr_ct { (num_of_wr <= 150); }

    virtual task body();
      start_addr = base_addr + `TX_FIFO_REG;
      for (int i = 0; i < num_of_wr; i++) begin
      write_data = write_data + i;
      `uvm_do_with(req, { req.address == start_addr; req.data == write_data; req.direction == WRITE; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
      end
    endtask
  
  function void post_randomize();
      write_data = rand_data;
  endfunction
endclass : ahb_to_uart_wr

// writes 0-150 data in SPI TX FIFO
class ahb_to_spi_wr extends uvm_sequence #(ahb_transfer);

    function new(string name="ahb_to_spi_wr");
      super.new(name);
    endfunction

    // Register sequence with a sequencer 
    `uvm_object_utils(ahb_to_spi_wr)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    rand bit unsigned[31:0] rand_data;
    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;
    bit [`AHB_ADDR_WIDTH-1:0] start_addr;
    rand bit [`AHB_DATA_WIDTH-1:0] write_data;
    rand int unsigned num_of_wr;
    constraint num_of_wr_ct { (num_of_wr <= 150); }

    virtual task body();
      start_addr = base_addr + `SPI_TX0_REG;
      for (int i = 0; i < num_of_wr; i++) begin
      write_data = write_data + i;
      `uvm_do_with(req, { req.address == start_addr; req.data == write_data; req.direction == WRITE; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
      end
    endtask
  
  function void post_randomize();
      write_data = rand_data;
  endfunction
endclass : ahb_to_spi_wr

// writes 1 data in GPIO TX REG
class ahb_to_gpio_wr extends uvm_sequence #(ahb_transfer);

    function new(string name="ahb_to_gpio_wr");
      super.new(name);
    endfunction

    // Register sequence with a sequencer 
    `uvm_object_utils(ahb_to_gpio_wr)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    rand bit unsigned[31:0] rand_data;
    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;
    bit [`AHB_ADDR_WIDTH-1:0] start_addr;
    rand bit [`AHB_DATA_WIDTH-1:0] write_data;

    virtual task body();
      start_addr = base_addr + `GPIO_OUTPUT_VALUE_REG;
      `uvm_do_with(req, { req.address == start_addr; req.data == write_data; req.direction == WRITE; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
    endtask
  
  function void post_randomize();
      write_data = rand_data;
  endfunction
endclass : ahb_to_gpio_wr

// Low Power CPF test
class shutdown_dut extends uvm_sequence #(ahb_transfer);

    // Register sequence with a sequencer 
    `uvm_object_utils(shutdown_dut)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    function new(string name="shutdown_dut");
      super.new(name);
    endfunction
  
    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;

    bit [`AHB_ADDR_WIDTH-1:0] start_addr;

    rand bit [`AHB_DATA_WIDTH-1:0] write_data;
    constraint uart_smc_shut { (write_data >= 1 && write_data <= 3); }

    virtual task body();
      start_addr = 32'h00860004;
      //write_data = 32'h01;

     if (write_data == 1)
      `uvm_info("SEQ", ("shutdown_dut sequence is shutting down UART "), UVM_MEDIUM)
     else if (write_data == 2) 
      `uvm_info("SEQ", ("shutdown_dut sequence is shutting down SMC "), UVM_MEDIUM)
     else if (write_data == 3) 
      `uvm_info("SEQ", ("shutdown_dut sequence is shutting down UART and SMC "), UVM_MEDIUM)

      `uvm_do_with(req, { req.address == start_addr; req.data == write_data; req.direction == WRITE; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
    endtask
  
endclass :  shutdown_dut

// Low Power CPF test
class poweron_dut extends uvm_sequence #(ahb_transfer);

    // Register sequence with a sequencer 
    `uvm_object_utils(poweron_dut)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    function new(string name="poweron_dut");
      super.new(name);
    endfunction
  
    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;

    bit [`AHB_ADDR_WIDTH-1:0] start_addr;
    bit [`AHB_DATA_WIDTH-1:0] write_data;

    virtual task body();
      start_addr = 32'h00860004;
      write_data = 32'h00;
      `uvm_info("SEQ", ("poweron_dut sequence is switching on PDurt"), UVM_MEDIUM)
      `uvm_do_with(req, { req.address == start_addr; req.data == write_data; req.direction == WRITE; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
    endtask
  
endclass : poweron_dut

// Reads UART RX FIFO
class intrpt_seq extends uvm_sequence #(ahb_transfer);

    // Register sequence with a sequencer 
    `uvm_object_utils(intrpt_seq)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    function new(string name="intrpt_seq");
      super.new(name);
    endfunction

    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;
    rand bit [`AHB_ADDR_WIDTH-1:0] read_addr;
    rand int unsigned num_of_rd;
    constraint num_of_rd_ct { (num_of_rd <= 150); }

    virtual task body();
      bit [`AHB_DATA_WIDTH-1:0] read_data;

      for (int i = 0; i < num_of_rd; i++) begin
        read_addr = base_addr + `RX_FIFO_REG;      //rx fifo address
        `uvm_do_with(req, { req.address == read_addr; req.data == read_data; req.direction == READ; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
        `uvm_info("SEQ", $sformatf("Read RX_FIFO_REG DATA is `x%0h", read_data), UVM_HIGH)
      end
    endtask
  
endclass : intrpt_seq

// Reads SPI RX REG
class read_spi_rx_reg extends uvm_sequence #(ahb_transfer);

    // Register sequence with a sequencer 
    `uvm_object_utils(read_spi_rx_reg)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    function new(string name="read_spi_rx_reg");
      super.new(name);
    endfunction

    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;
    rand bit [`AHB_ADDR_WIDTH-1:0] read_addr;
    rand int unsigned num_of_rd;
    constraint num_of_rd_ct { (num_of_rd <= 150); }

    virtual task body();
      bit [`AHB_DATA_WIDTH-1:0] read_data;

      for (int i = 0; i < num_of_rd; i++) begin
        read_addr = base_addr + `SPI_RX0_REG;
        `uvm_do_with(req, { req.address == read_addr; req.data == read_data; req.direction == READ; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
        `uvm_info("SEQ", $sformatf("Read DATA is `x%0h", read_data), UVM_HIGH)
      end
    endtask
  
endclass : read_spi_rx_reg

// Reads GPIO INPUT_VALUE REG
class read_gpio_rx_reg extends uvm_sequence #(ahb_transfer);

    // Register sequence with a sequencer 
    `uvm_object_utils(read_gpio_rx_reg)
    `uvm_declare_p_sequencer(ahb_pkg::ahb_master_sequencer)    

    function new(string name="read_gpio_rx_reg");
      super.new(name);
    endfunction

    rand bit [`AHB_ADDR_WIDTH-1:0] base_addr;
    rand bit [`AHB_ADDR_WIDTH-1:0] read_addr;

    virtual task body();
      bit [`AHB_DATA_WIDTH-1:0] read_data;

      read_addr = base_addr + `GPIO_INPUT_VALUE_REG;
      `uvm_do_with(req, { req.address == read_addr; req.data == read_data; req.direction == READ; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
      `uvm_info("SEQ", $sformatf("Read DATA is `x%0h", read_data), UVM_HIGH)
    endtask
  
endclass : read_gpio_rx_reg

