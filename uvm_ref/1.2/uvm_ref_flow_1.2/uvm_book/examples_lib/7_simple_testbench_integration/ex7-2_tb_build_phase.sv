/****************************************************************
  Example 7-2: UART Controller Testbench Build Phase

  This is just a code sample.
  The complete example is in: ex7-1_uart_ctrl_tb.sv

  To run:   %  irun -f run.f ex7-1_uart_ctrl_tb.sv
****************************************************************/
function void uart_ctrl_tb::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Create UVC configuration if it has not already been set
  if (apb_cfg == null) begin
    apb_cfg = apb_config::type_id::create("apb_cfg", this);
    apb_cfg.add_master("master", UVM_ACTIVE);
    apb_cfg.add_slave("slave0", 32'h00000000, 32'h81FFFFFF, 0, UVM_PASSIVE);
  end
  if (uart_cfg == null) begin
    uart_cfg = uart_config::type_id::create("uart_cfg", this);
  end
  uvm_config_db#(apb_config)::set(this, "apb0*", "cfg", apb_cfg);
  uvm_config_db#(uart_config)::set(this, "uart0*", "cfg", uart_cfg);
  uvm_config_db#(uart_config)::set(this, "*scbd*", "uart_cfg", uart_cfg);
  uvm_config_db#(apb_slave_config)::set(this, "*scbd*", "slave_cfg", apb_cfg.slave_configs[0]);
//  uvm_config_object::set(this, "apb0", "cfg", apb_cfg);
//  uvm_config_object::set(this, "uart0", "cfg", uart_cfg);
//  uvm_config_object::set(this, "*scbd*", "uart_cfg", uart_cfg);
//  uvm_config_object::set(this, "*scbd*", "slave_cfg", apb_cfg.slave_configs[0]);

  // Create sub-components
  apb0 = apb_env::type_id::create("apb0", this);
  uart0 = uart_env::type_id::create("uart0", this);
  virtual_sequencer = uart_ctrl_virtual_sequencer::type_id::create("virtual_sequencer", this);
  tx_scbd = uart_ctrl_tx_scbd::type_id::create("tx_scbd", this);
  rx_scbd = uart_ctrl_rx_scbd::type_id::create("rx_scbd", this);
endfunction : build_phase
