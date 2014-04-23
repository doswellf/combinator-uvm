/*****************************************************************
  FILE : uart_ctrl_config.sv
******************************************************************
  This file contains multiple configuration classes:
    apb_config
       master_config
       slave_configs[N]
    uart_config
******************************************************************/

`ifndef UART_CTRL_CONFIG_SV
`define UART_CTRL_CONFIG_SV

// UART Controller Configuration Class
class uart_ctrl_config extends uvm_object;

  apb_config apb_cfg;
  uart_config uart_cfg;

  `uvm_object_utils_begin(uart_ctrl_config)
      `uvm_field_object(apb_cfg, UVM_DEFAULT)
      `uvm_field_object(uart_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "uart_ctrl_config");
    super.new(name);
    uart_cfg = uart_config::type_id::create("uart_cfg");
    apb_cfg = apb_config::type_id::create("apb_cfg"); 
  endfunction : new

endclass : uart_ctrl_config

//================================================================
class default_uart_ctrl_config extends uart_ctrl_config;

  `uvm_object_utils(default_uart_ctrl_config)

  function new(string name = "default_uart_ctrl_config");
    super.new(name);
    uart_cfg = uart_config::type_id::create("uart_cfg");
    apb_cfg = apb_config::type_id::create("apb_cfg"); 
    apb_cfg.add_slave("slave0", 32'h0000_0000, 32'h7FFF_FFFF, 0, UVM_ACTIVE);
    apb_cfg.add_master("master", UVM_ACTIVE);
  endfunction

endclass : default_uart_ctrl_config

`endif // UART_CTRL_CONFIG_SV
