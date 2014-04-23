/*-------------------------------------------------------------------------
File name   : gpio_config.sv
Title       : gpio environment configuration file
Project     : UVM SystemVerilog Cluster Level Verification
Created     :
Description :
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


`ifndef GPIO_CFG_SVH
`define GPIO_CFG_SVH

class gpio_config extends uvm_object;

  function new (string name = "");
    super.new(name);
  endfunction

  uvm_active_passive_enum  active_passive = UVM_ACTIVE;

  `uvm_object_utils_begin(gpio_config)
    `uvm_field_enum(uvm_active_passive_enum, active_passive, UVM_ALL_ON)
   `uvm_object_utils_end

endclass

`endif

