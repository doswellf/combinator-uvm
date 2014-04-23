/*-------------------------------------------------------------------------
File name   : uart_ctrl_monitor.sv
Title       : UART Controller Monitor
Project     :
Created     :
Description : Module monitor
Notes       : 
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/
// TLM Port Declarations
`uvm_analysis_imp_decl(_rx)
`uvm_analysis_imp_decl(_tx)
`uvm_analysis_imp_decl(_cfg)
//`uvm_analysis_imp_decl(_apb)

class uart_ctrl_monitor extends uvm_monitor;

  // Virtual interface to DUT signals if necessary (OPTIONAL)
  virtual interface uart_ctrl_internal_if vif;

  time rx_time_q[$];
  time tx_time_q[$];
  time tx_time_out, tx_time_in, rx_time_out, rx_time_in, clk_period;

  // UART Controller Configuration Information
  uart_ctrl_config cfg;

  // UART Controller coverage
  uart_ctrl_cover uart_cover;

  // Scoreboards
  uart_ctrl_tx_scbd tx_scbd;
  uart_ctrl_rx_scbd rx_scbd;

  // TLM Connections to the interface UVC monitors
  uvm_analysis_imp_apb #(apb_transfer, uart_ctrl_monitor) apb_in;
  uvm_analysis_imp_rx #(uart_frame, uart_ctrl_monitor) uart_rx_in;
  uvm_analysis_imp_tx #(uart_frame, uart_ctrl_monitor) uart_tx_in;
  uvm_analysis_imp_cfg #(uart_config, uart_ctrl_monitor) uart_cfg_in;

  // TLM Connections to other Components (Scoreboard, updated config)
//  uvm_analysis_port #(uart_config) uart_cfg_out;
  uvm_analysis_port #(apb_transfer) apb_out;
  uvm_analysis_port #(uart_frame) uart_rx_out;
  uvm_analysis_port #(uart_frame) uart_tx_out;

  `uvm_component_utils(uart_ctrl_monitor)

  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    create_tlm_ports(); // Create TLM Ports
  endfunction: new

  task run();
    @(posedge vif.clock) clk_period = $time;
    @(posedge vif.clock) clk_period = $time - clk_period;
  endtask : run
 
  // Additional class methods
  extern virtual function void create_tlm_ports();
  extern virtual function void build();
  extern virtual function void connect();
  extern virtual function void write_rx(uart_frame frame);
  extern virtual function void write_tx(uart_frame frame);
  extern virtual function void write_apb(apb_transfer transfer);
  extern virtual function void write_cfg(uart_config uart_cfg);
  extern virtual function void update_config(uart_ctrl_config uart_ctrl_cfg);
  extern virtual function void set_slave_config(apb_slave_config slave_cfg);
  extern virtual function void set_uart_config(uart_config uart_cfg);
endclass : uart_ctrl_monitor

function void uart_ctrl_monitor::create_tlm_ports();
  //uart_cfg_out = new("uart_cfg_out", this);
  apb_in = new("apb_in", this);
  apb_out = new("apb_out", this);
  uart_rx_in = new("uart_rx_in", this);
  uart_rx_out = new("uart_rx_out", this);
  uart_tx_in = new("uart_tx_in", this);
  uart_tx_out = new("uart_tx_out", this);
endfunction: create_tlm_ports

function void uart_ctrl_monitor::build();
  super.build();
  uart_cover = uart_ctrl_cover::type_id::create("uart_cover",this);
  if (cfg == null) begin
    `uvm_info(get_type_name(), "cfg is null...creating ", UVM_MEDIUM)
    cfg = uart_ctrl_config::type_id::create("cfg", this);
    set_config_object("tx_scbd", "cfg", cfg);
    set_config_object("rx_scbd", "cfg", cfg);
  end
  tx_scbd = uart_ctrl_tx_scbd::type_id::create("tx_scbd",this);
  rx_scbd = uart_ctrl_rx_scbd::type_id::create("rx_scbd",this);

//chenthil
// tx_scbd.slave_cfg = cfg;
// rx_scbd.slave_cfg = cfg;
endfunction : build
   
function void uart_ctrl_monitor::connect();
  super.connect();
  apb_out.connect(tx_scbd.apb_match);
  uart_tx_out.connect(tx_scbd.uart_add);
  apb_out.connect(rx_scbd.apb_add);
  uart_rx_out.connect(rx_scbd.uart_match);
endfunction : connect

// implement UART Rx analysis port
function void uart_ctrl_monitor::write_rx(uart_frame frame);
  uart_rx_out.write(frame);
  rx_time_q.push_front($time); 
endfunction : write_rx
   
// implement UART Tx analysis port
function void uart_ctrl_monitor::write_tx(uart_frame frame);
  uart_tx_out.write(frame);
  tx_time_in = tx_time_q.pop_back();
  tx_time_out = ($time-tx_time_in)/clk_period;
endfunction : write_tx

// implement UART Config analysis port
function void uart_ctrl_monitor::write_cfg(uart_config uart_cfg);
   set_uart_config(uart_cfg);
endfunction : write_cfg

  // implement APB analysis port 
function void uart_ctrl_monitor::write_apb(apb_transfer transfer);
// chenthil  if (transfer.addr ==  cfg.apb_cfg.slave_configs[0].start_address + 'h00) 
    apb_out.write(transfer);
  if ((transfer.direction == APB_READ)  && (transfer.addr == `RX_FIFO_REG))
     begin
       rx_time_in = rx_time_q.pop_back();
       rx_time_out = ($time-rx_time_in)/clk_period;
     end
  else if ((transfer.direction == APB_WRITE)  && (transfer.addr == `TX_FIFO_REG))
     begin
       tx_time_q.push_front($time); 
     end
    
endfunction : write_apb

function void uart_ctrl_monitor::update_config(uart_ctrl_config uart_ctrl_cfg);
  `uvm_info(get_type_name(), {"Updating Config\n", uart_ctrl_cfg.sprint}, UVM_HIGH)
   cfg = uart_ctrl_cfg;
   tx_scbd.slave_cfg = uart_ctrl_cfg.apb_cfg.slave_configs[0];
   tx_scbd.uart_cfg = uart_ctrl_cfg.uart_cfg;
   rx_scbd.slave_cfg = uart_ctrl_cfg.apb_cfg.slave_configs[0];
   rx_scbd.uart_cfg = uart_ctrl_cfg.uart_cfg;
endfunction : update_config

function void uart_ctrl_monitor::set_slave_config(apb_slave_config slave_cfg);
   cfg.apb_cfg.slave_configs[0] = slave_cfg;
   tx_scbd.slave_cfg = slave_cfg;
   rx_scbd.slave_cfg = slave_cfg;
endfunction : set_slave_config

function void uart_ctrl_monitor::set_uart_config(uart_config uart_cfg);
   cfg.uart_cfg     = uart_cfg;
   tx_scbd.uart_cfg = uart_cfg;
   rx_scbd.uart_cfg = uart_cfg;
endfunction : set_uart_config
