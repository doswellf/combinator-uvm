/***********************************************************************
 Example 10-1:  UART Controller Monitor

 Kit Location:  $UVM_REF_HOME/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_monitor.sv
***********************************************************************/

// TLM Port Declarations
`uvm_analysis_imp_decl(_rx)
`uvm_analysis_imp_decl(_tx)
`uvm_analysis_imp_decl(_cfg)

class uart_ctrl_monitor extends uvm_monitor;

  // Virtual interface to DUT signals if necessary (OPTIONAL)
  virtual interface uart_ctrl_internal_if vif;

  // UART Controller Configuration Information
  uart_ctrl_config cfg;

  // Tx and Rx Scoreboards
  uart_ctrl_tx_scbd tx_scbd;
  uart_ctrl_rx_scbd rx_scbd;
  // UART Controller coverage
  uart_ctrl_cover uart_cover;

  // TLM Connections to the interface UVC monitors
  uvm_analysis_imp_apb #(apb_transfer, uart_ctrl_monitor) apb_in;
  uvm_analysis_imp_rx #(uart_frame, uart_ctrl_monitor) uart_rx_in;
  uvm_analysis_imp_tx #(uart_frame, uart_ctrl_monitor) uart_tx_in;
  uvm_analysis_imp_cfg #(uart_config, uart_ctrl_monitor) uart_cfg_in;

  // TLM Connections to other Components (Scoreboard, updated config)
  uvm_analysis_port #(apb_transfer) apb_out;
  uvm_analysis_port #(uart_frame) uart_rx_out;
  uvm_analysis_port #(uart_frame) uart_tx_out;

  // Track times for checking/analysis
  time rx_time_q[$], tx_time_q[$];
  time tx_time_out, tx_time_in, rx_time_out, rx_time_in, clk_period;

  `uvm_component_utils_begin(uart_ctrl_monitor)
     `uvm_field_object(cfg, UVM_ALL_ON | UVM_REFERENCE)
  `uvm_component_utils_end

  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    create_tlm_ports(); // Create TLM Ports
  endfunction: new

  task run_phase(uvm_phase phase);
    @(posedge vif.clock) clk_period = $time;
    @(posedge vif.clock) clk_period = $time - clk_period;
  endtask : run_phase
 
  // Additional class methods
  extern virtual function void create_tlm_ports();
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void write_rx(uart_frame frame);
  extern virtual function void write_tx(uart_frame frame);
  extern virtual function void write_apb(apb_transfer transfer);
  extern virtual function void write_cfg(uart_config uart_cfg);
  extern virtual function void update_config(uart_ctrl_config uart_ctrl_cfg, int index);
  extern virtual function void set_slave_config(apb_slave_config slave_cfg, int index);
  extern virtual function void set_uart_config(uart_config uart_cfg);
endclass : uart_ctrl_monitor

function void uart_ctrl_monitor::create_tlm_ports();
  apb_in = new("apb_in", this);
  apb_out = new("apb_out", this);
  uart_rx_in = new("uart_rx_in", this);
  uart_rx_out = new("uart_rx_out", this);
  uart_tx_in = new("uart_tx_in", this);
  uart_tx_out = new("uart_tx_out", this);
endfunction: create_tlm_ports

function void uart_ctrl_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  uart_cover = uart_ctrl_cover::type_id::create("uart_cover",this);

  // Get the configuration for this component
  //if (!uvm_config_db#(uart_ctrl_config)::get(this, "", "cfg", cfg)) begin
  if (cfg==null) begin
    `uvm_info("NOCONFIG", "uart_ctrl_cfg is null...creating ", UVM_MEDIUM)
    cfg = uart_ctrl_config::type_id::create("cfg", this);
    //set_config_object("tx_scbd", "cfg", cfg);
    //set_config_object("rx_scbd", "cfg", cfg);
  end
  //uvm_config_db#(uart_config)::set(this, "*x_scbd", "uart_cfg", cfg.uart_cfg);
  //uvm_config_db#(apb_slave_config)::set(this, "*x_scbd", "apb_slave_cfg", cfg.apb_cfg.slave_configs[0]);
  uvm_config_object::set(this, "*x_scbd", "uart_cfg", cfg.uart_cfg);
  uvm_config_object::set(this, "*x_scbd", "apb_slave_cfg", cfg.apb_cfg.slave_configs[0]);
  tx_scbd = uart_ctrl_tx_scbd::type_id::create("tx_scbd",this);
  rx_scbd = uart_ctrl_rx_scbd::type_id::create("rx_scbd",this);
endfunction : build_phase
   
function void uart_ctrl_monitor::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // Get the virtual interface for this component
  if (!uvm_config_db#(virtual uart_ctrl_internal_if)::get(this, "", "vif", vif))
      `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
  apb_out.connect(tx_scbd.apb_match);
  uart_tx_out.connect(tx_scbd.uart_add);
  apb_out.connect(rx_scbd.apb_add);
  uart_rx_out.connect(rx_scbd.uart_match);
endfunction : connect_phase

// implement UART Rx analysis port
function void uart_ctrl_monitor::write_rx(uart_frame frame);
  uart_rx_out.write(frame);
  tx_time_in = tx_time_q.pop_back();
  tx_time_out = ($time-tx_time_in)/clk_period;
endfunction : write_rx
   
// implement UART Tx analysis port
function void uart_ctrl_monitor::write_tx(uart_frame frame);
  uart_tx_out.write(frame);
  rx_time_q.push_front($time); 
endfunction : write_tx

// implement UART Config analysis port
function void uart_ctrl_monitor::write_cfg(uart_config uart_cfg);
   set_uart_config(uart_cfg);
endfunction : write_cfg

  // implement APB analysis port 
function void uart_ctrl_monitor::write_apb(apb_transfer transfer);
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

function void uart_ctrl_monitor::update_config(uart_ctrl_config uart_ctrl_cfg, int index);
  `uvm_info(get_type_name(), {"Updating Config\n", uart_ctrl_cfg.sprint}, UVM_HIGH)
   cfg = uart_ctrl_cfg;
   tx_scbd.slave_cfg = uart_ctrl_cfg.apb_cfg.slave_configs[index];
   tx_scbd.uart_cfg = uart_ctrl_cfg.uart_cfg;
   rx_scbd.slave_cfg = uart_ctrl_cfg.apb_cfg.slave_configs[index];
   rx_scbd.uart_cfg = uart_ctrl_cfg.uart_cfg;
endfunction : update_config

function void uart_ctrl_monitor::set_slave_config(apb_slave_config slave_cfg, int index);
   cfg.apb_cfg.slave_configs[index] = slave_cfg;
   tx_scbd.slave_cfg = slave_cfg;
   rx_scbd.slave_cfg = slave_cfg;
endfunction : set_slave_config

function void uart_ctrl_monitor::set_uart_config(uart_config uart_cfg);
   cfg.uart_cfg     = uart_cfg;
   tx_scbd.uart_cfg = uart_cfg;
   rx_scbd.uart_cfg = uart_cfg;
endfunction : set_uart_config
