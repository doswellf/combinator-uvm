/*-------------------------------------------------------------------------
File name   : uart_ctrl_scoreboard.sv
Title       : APB - UART Scoreboard
Project     :
Created     :
Description : Scoreboard for data integrity check between APB UVC and UART UVC
Notes       : Two similar scoreboards one for read and one for write
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/
`uvm_analysis_imp_decl(_apb)
`uvm_analysis_imp_decl(_uart)

class uart_ctrl_tx_scbd extends uvm_scoreboard;
  bit [7:0] data_to_apb[$];
  bit [7:0] temp1;

  // Config Information 
  uart_pkg::uart_config uart_cfg;
  apb_pkg::apb_slave_config slave_cfg;

  `uvm_component_utils_begin(uart_ctrl_tx_scbd)
     `uvm_field_object(slave_cfg, UVM_DEFAULT)
     `uvm_field_object(uart_cfg, UVM_DEFAULT)
  `uvm_component_utils_end

  uvm_analysis_imp_apb #(apb_pkg::apb_transfer, uart_ctrl_tx_scbd) apb_match;
  uvm_analysis_imp_uart #(uart_pkg::uart_frame, uart_ctrl_tx_scbd) uart_add;
   
  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    uart_add  = new("uart_add", this);
    apb_match = new("apb_match", this);
  endfunction : new

  // implement UART Tx analysis port from reference model
  virtual function void write_uart(uart_pkg::uart_frame frame);
    data_to_apb.push_back(frame.payload);	
  endfunction : write_uart
     
  // implement APB READ analysis port from reference model
  virtual function void write_apb(input apb_pkg::apb_transfer transfer);

    if ((transfer.addr ==   (slave_cfg.start_address + `RX_FIFO_REG)) && (transfer.direction == apb_pkg::APB_READ))
      begin
          temp1 = data_to_apb.pop_front();
       
        if (temp1 == transfer.data ) 
          `uvm_info("SCRBD", $sformatf("####### PASS : APB RECEIVED CORRECT DATA from %s  expected = 'h%0h, received = 'h%0h", slave_cfg.name, temp1, transfer.data), UVM_MEDIUM)
        else
        begin
          `uvm_error("SCRBD", $sformatf("####### FAIL : APB RECEIVED WRONG DATA from %s", slave_cfg.name))
          `uvm_info("SCRBD", $sformatf("expected = 'h%0h, received = 'h%0h", temp1, transfer.data), UVM_LOW)
        end
      end
  endfunction : write_apb
   
  function void assign_cfg(uart_pkg::uart_config u_cfg);
    uart_cfg = u_cfg;
  endfunction : assign_cfg

  function void update_config(uart_pkg::uart_config u_cfg);
    `uvm_info(get_type_name(), {"Updating Config\n", u_cfg.sprint}, UVM_HIGH)
    uart_cfg = u_cfg;
  endfunction : update_config

endclass : uart_ctrl_tx_scbd

class uart_ctrl_rx_scbd extends uvm_scoreboard;
  bit [7:0] data_from_apb[$];
  bit [7:0] data_to_apb[$]; // Relevant for Remoteloopback case only
  bit div_en;

  bit [7:0] temp1;
  bit [7:0] mask;

  uart_pkg::uart_config uart_cfg;
  apb_pkg::apb_slave_config slave_cfg;

  `uvm_component_utils_begin(uart_ctrl_rx_scbd)
     `uvm_field_object(slave_cfg, UVM_DEFAULT | UVM_REFERENCE)
     `uvm_field_object(uart_cfg, UVM_DEFAULT | UVM_REFERENCE)
  `uvm_component_utils_end

  uvm_analysis_imp_apb #(apb_pkg::apb_transfer, uart_ctrl_rx_scbd) apb_add;
  uvm_analysis_imp_uart #(uart_pkg::uart_frame, uart_ctrl_rx_scbd) uart_match;
   
  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    uart_match = new("uart_match", this);
    apb_add    = new("apb_add", this);
  endfunction : new
   
  // implement APB WRITE analysis port from reference model
  virtual function void write_apb(input apb_pkg::apb_transfer transfer);
    `uvm_info("SCRBD",
              $sformatf("write_apb called with addr = 'h%0h and data = 'h%0h",
              transfer.addr, transfer.data), UVM_HIGH)
    if ((transfer.addr == (slave_cfg.start_address + `LINE_CTRL)) &&
        (transfer.direction == apb_pkg::APB_WRITE)) begin
      div_en = transfer.data[7];
      `uvm_info("SCRBD",
              $sformatf("LINE_CTRL Write with addr = 'h%0h and data = 'h%0h div_en = %0b",
              transfer.addr, transfer.data, div_en ), UVM_HIGH)
    end

    if (!div_en) begin
      if ((transfer.addr == (slave_cfg.start_address + `TX_FIFO_REG)) &&
          (transfer.direction == apb_pkg::APB_WRITE)) begin 
        `uvm_info("SCRBD",
               $sformatf("write_apb called pushing into queue with data = 'h%0h",
               transfer.data ), UVM_HIGH)
        data_from_apb.push_back(transfer.data);
      end
    end
  endfunction : write_apb
   
  // implement UART Rx analysis port from reference model
  virtual function void write_uart( uart_pkg::uart_frame frame);
    mask = calc_mask();

    //In case of remote loopback, the data does not get into the rx/fifo and it gets 
    // loopbacked to ua_txd. 
    data_to_apb.push_back(frame.payload);	

      temp1 = data_from_apb.pop_front();

    if ((temp1 & mask) == frame.payload) 
      `uvm_info("SCRBD", $sformatf("####### PASS : %s RECEIVED CORRECT DATA expected = 'h%0h, received = 'h%0h", slave_cfg.name, (temp1 & mask), frame.payload), UVM_MEDIUM)
    else
    begin
      `uvm_error("SCRBD", $sformatf("####### FAIL : %s RECEIVED WRONG DATA", slave_cfg.name))
      `uvm_info("SCRBD", $sformatf("expected = 'h%0h, received = 'h%0h", temp1, frame.payload), UVM_LOW)
    end
  endfunction : write_uart
   
  function void assign_cfg(uart_pkg::uart_config u_cfg);
     uart_cfg = u_cfg;
  endfunction : assign_cfg
   
  function void update_config(uart_pkg::uart_config u_cfg);
   `uvm_info(get_type_name(), {"Updating Config\n", u_cfg.sprint}, UVM_HIGH)
    uart_cfg = u_cfg;
  endfunction : update_config

  function bit[7:0] calc_mask();
    case (uart_cfg.char_len_val)
      6: return 8'b00111111;
      7: return 8'b01111111;
      8: return 8'b11111111;
      default: return 8'hff;
    endcase
  endfunction : calc_mask

endclass : uart_ctrl_rx_scbd
