/*---------------------------------------------------------------------
File name   : apb_subsystem_reg_rdb.sv
Title       : Reg Mem data base
Project     :
Created     :
Description : reg data base for APB Subsystem
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
 
//////////////////////////////////////////////////////////////////////////////
// Address_map definition
//////////////////////////////////////////////////////////////////////////////
class apb_ss_reg_model_c extends uvm_reg_block;

  //rand uart_ctrl_rf_c uart0_rf;
  //rand uart_ctrl_rf_c uart1_rf;
  rand uart_ctrl_reg_model_c uart0_rm;
  rand uart_ctrl_reg_model_c uart1_rm;
  rand spi_regfile spi_rf;
  rand gpio_regfile gpio_rf;

  function void build();
    // Now define address mappings
/*
    default_map = create_map("default_map", 0, 1, UVM_LITTLE_ENDIAN);
    uart0_rf = uart_ctrl_rf_c::type_id::create("uart0_rf", , get_full_name());
    uart0_rf.configure(this, "rf0");
    uart0_rf.build();
    uart0_rf.lock_model();
    default_map.add_submap(uart0_rf.default_map, `UVM_REG_ADDR_WIDTH'h81_0000);
    set_hdl_path_root("reg_model");
    uart1_rf = uart_ctrl_rf_c::type_id::create("uart1_rf", , get_full_name());
    uart1_rf.configure(this, "rf1");
    uart1_rf.build();
    uart1_rf.lock_model();
    default_map.add_submap(uart1_rf.default_map, `UVM_REG_ADDR_WIDTH'h88_0000);
*/
    default_map = create_map("default_map", 0, 1, UVM_LITTLE_ENDIAN);
    uart0_rm = uart_ctrl_reg_model_c::type_id::create("uart0_rm", , get_full_name());
    uart0_rm.configure(this, "rf0");
    uart0_rm.build();
    uart0_rm.lock_model();
    default_map.add_submap(uart0_rm.default_map, `UVM_REG_ADDR_WIDTH'h81_0000);
    set_hdl_path_root("reg_model");
    uart1_rm = uart_ctrl_reg_model_c::type_id::create("uart1_rm", , get_full_name());
    uart1_rm.configure(this, "rf1");
    uart1_rm.build();
    uart1_rm.lock_model();
    default_map.add_submap(uart1_rm.default_map, `UVM_REG_ADDR_WIDTH'h88_0000);
    set_hdl_path_root("reg_model1");

    spi_rf = spi_regfile::type_id::create("spi_rf", , get_full_name());
    spi_rf.configure(this, "rf2");
    spi_rf.build();
    spi_rf.lock_model();
    default_map.add_submap(spi_rf.default_map, `UVM_REG_ADDR_WIDTH'h80_0000);
    set_hdl_path_root("apb_spi_addr_map_c");
    gpio_rf = gpio_regfile::type_id::create("gpio_rf", , get_full_name());
    gpio_rf.configure(this, "rf3");
    gpio_rf.build();
    gpio_rf.lock_model();
    default_map.add_submap(gpio_rf.default_map, `UVM_REG_ADDR_WIDTH'h82_0000);
    set_hdl_path_root("apb_gpio_addr_map_c");
    this.lock_model();
  endfunction

  `uvm_object_utils(apb_ss_reg_model_c)

  function new(input string name="unnamed-apb_ss_reg_model_c");
    super.new(name, UVM_NO_COVERAGE);
  endfunction

endclass : apb_ss_reg_model_c

