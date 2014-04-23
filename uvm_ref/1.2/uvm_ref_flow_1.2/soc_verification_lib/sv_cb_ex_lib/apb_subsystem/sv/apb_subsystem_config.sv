/*-------------------------------------------------------------------------
File name   : apb_subsystem_config.svh
Title       : APB Subsystem configuration
Project     :
Created     :
Description : This file contains multiple configuration classes:
                apb_config
                   master_config
                   slave_configs[N]
                uart_config
Notes       : 
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


`ifndef APB_SUBSYSTEM_CTRL_CONFIG_SV
`define APB_SUBSYSTEM_CTRL_CONFIG_SV

// APB Subsystem Configuration Class
class apb_subsystem_config extends uvm_object;

  uart_ctrl_config uart_cfg0;
  uart_ctrl_config uart_cfg1;
  spi_pkg::spi_config spi_cfg;  //Sharon - ok to use as is, as a shortcut - document this
  gpio_pkg::gpio_config gpio_cfg;

  `uvm_object_utils_begin(apb_subsystem_config)
      `uvm_field_object(uart_cfg0, UVM_DEFAULT)
      `uvm_field_object(uart_cfg1, UVM_DEFAULT)
      `uvm_field_object(spi_cfg, UVM_DEFAULT)
      `uvm_field_object(gpio_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "apb_subsystem_config");
    super.new(name);
    uart_cfg0 = uart_ctrl_config::type_id::create("uart_cfg0");
    uart_cfg1 = uart_ctrl_config::type_id::create("uart_cfg1");
    spi_cfg   = spi_pkg::spi_config::type_id::create("spi_cfg"); 
    gpio_cfg  = gpio_pkg::gpio_config::type_id::create("gpio_cfg"); 
  endfunction : new

endclass : apb_subsystem_config

//================================================================
class default_apb_subsystem_config extends apb_subsystem_config;

  `uvm_object_utils(default_apb_subsystem_config)

  function new(string name = "default_apb_subsystem_config");
    super.new(name);
    uart_cfg0 = uart_ctrl_config::type_id::create("uart_cfg0");
    uart_cfg1 = uart_ctrl_config::type_id::create("uart_cfg1");
    spi_cfg   = spi_pkg::spi_config::type_id::create("spi_cfg"); 
    gpio_cfg  = gpio_pkg::gpio_config::type_id::create("gpio_cfg"); 
    uart_cfg0.apb_cfg.add_master("master", UVM_PASSIVE);
    uart_cfg0.apb_cfg.add_slave("spi0",  `AM_SPI0_BASE_ADDRESS,  `AM_SPI0_END_ADDRESS,  0, UVM_PASSIVE);
    uart_cfg0.apb_cfg.add_slave("uart0", `AM_UART0_BASE_ADDRESS, `AM_UART0_END_ADDRESS, 0, UVM_PASSIVE);
    uart_cfg0.apb_cfg.add_slave("gpio0", `AM_GPIO0_BASE_ADDRESS, `AM_GPIO0_END_ADDRESS, 0, UVM_PASSIVE);
    uart_cfg0.apb_cfg.add_slave("uart1", `AM_UART1_BASE_ADDRESS, `AM_UART1_END_ADDRESS, 1, UVM_PASSIVE);
    uart_cfg1.apb_cfg.add_master("master", UVM_PASSIVE);
    uart_cfg1.apb_cfg.add_slave("spi0",  `AM_SPI0_BASE_ADDRESS,  `AM_SPI0_END_ADDRESS,  0, UVM_PASSIVE);
    uart_cfg1.apb_cfg.add_slave("uart0", `AM_UART0_BASE_ADDRESS, `AM_UART0_END_ADDRESS, 0, UVM_PASSIVE);
    uart_cfg1.apb_cfg.add_slave("gpio0", `AM_GPIO0_BASE_ADDRESS, `AM_GPIO0_END_ADDRESS, 0, UVM_PASSIVE);
    uart_cfg1.apb_cfg.add_slave("uart1", `AM_UART1_BASE_ADDRESS, `AM_UART1_END_ADDRESS, 1, UVM_PASSIVE);
  endfunction

endclass : default_apb_subsystem_config

`endif // UART_CTRL_CONFIG_SV

