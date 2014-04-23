/***********************************************************************
  Example 10-1:  UART Controller Monitor buid_phase and connect_phase

  This is an incomplete example.  It only shows the build_phase and
  connect_phase methods of the monitor.
***********************************************************************/
function void uart_ctrl_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  uart_cover = uart_ctrl_cover::type_id::create("uart_cover",this);

  // Get the configuration for this component
  if (cfg==null) begin
    if (!uvm_config_db#(uart_ctrl_config)::get(this, "", "cfg", cfg)) begin
    `uvm_info("NOCONFIG", "uart_ctrl_cfg is null...creating ", UVM_MEDIUM)
    cfg = uart_ctrl_config::type_id::create("cfg", this);
  end
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
