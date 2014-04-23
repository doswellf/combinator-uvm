/**********************************************************************
  Example 10-5: UART Controller Configuration Class

  %  irun -uvm ex10-5 uart_ctrl_config.sv
  
  Kit Location : $UVM_REF_HOME/soc_verification_libs/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_config.sv
*********************************************************************/
`include "ex10-4_uart_config.sv"
`include "../5_interface_uvcs/sv/apb_config.sv"

/*-------------------------------------------------------------------------
File name   : uart_ctrl_config.svh
Title       : UART Controller configuration
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
