/*******************************************************************************
  FILE : apb_config.sv
  This file contains multiple configuration classes:
    apb_slave_config - for configuring an APB slave device
    apb_master_config - for configuring an APB master device
    apb_config - has 1 master config and N slave config's
    default_apb_config - configures for 1 master and 2 slaves
*******************************************************************************/
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


`ifndef APB_CONFIG_SV
`define APB_CONFIG_SV

// APB Slave Configuration Information
class apb_slave_config extends uvm_object;
  string name;
  rand uvm_active_passive_enum is_active = UVM_ACTIVE;
  rand int start_address;
  rand int end_address;
  rand int psel_index;

  constraint addr_cst { start_address <= end_address; }
  constraint psel_cst { psel_index inside {[0:15]}; }

  `uvm_object_utils_begin(apb_slave_config)
    `uvm_field_string(name, UVM_DEFAULT)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
    `uvm_field_int(start_address, UVM_DEFAULT)
    `uvm_field_int(end_address, UVM_DEFAULT)
    `uvm_field_int(psel_index, UVM_DEFAULT)
  `uvm_object_utils_end

  // Constructor - UVM required syntax
  function new (string name = "apb_slave_config");
    super.new(name);
  endfunction

  // Checks to see if an address is in the configured range
  function bit check_address_range(int unsigned addr);
    return (!((start_address > addr) || (end_address < addr)));
  endfunction

endclass : apb_slave_config

// APB Master Configuration Information
class apb_master_config extends uvm_object;

  string name;
  uvm_active_passive_enum is_active = UVM_ACTIVE;

  function new (string name = "unnamed-apb_master_config");
    super.new(name);
  endfunction

  `uvm_object_utils_begin(apb_master_config)
    `uvm_field_string(name, UVM_DEFAULT)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
  `uvm_object_utils_end

endclass : apb_master_config

// APB Configuration Information 
class apb_config extends uvm_object;

  // APB has one master and N slaves
  apb_master_config master_config;
  apb_slave_config slave_configs[$];
  int num_slaves;

  `uvm_object_utils_begin(apb_config)
    `uvm_field_queue_object(slave_configs, UVM_DEFAULT)
    `uvm_field_object(master_config, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "unnamed-apb_config");
    super.new(name);
  endfunction

  // Additional class methods
  extern function void add_slave(string name, int start_addr, int end_addr,
            int psel_indx, uvm_active_passive_enum is_active = UVM_ACTIVE);
  extern function void add_master(string name,
            uvm_active_passive_enum is_active = UVM_ACTIVE);
  extern function int get_slave_psel_by_addr(int addr);
  extern function string get_slave_name_by_addr(int addr);
endclass  : apb_config

// apb_config - Creates and configures a slave agent config and adds to a queue
function void apb_config::add_slave(string name, int start_addr, int end_addr,
            int psel_indx, uvm_active_passive_enum is_active = UVM_ACTIVE);
  apb_slave_config tmp_slave_cfg;
  num_slaves++;
  tmp_slave_cfg = apb_slave_config::type_id::create("slave_config");
  tmp_slave_cfg.name = name;
  tmp_slave_cfg.start_address = start_addr;
  tmp_slave_cfg.end_address = end_addr;
  tmp_slave_cfg.psel_index = psel_indx;
  tmp_slave_cfg.is_active = is_active;
  
  slave_configs.push_back(tmp_slave_cfg);
endfunction : add_slave

// apb_config - Creates and configures a master agent configuration
function void apb_config::add_master(string name, uvm_active_passive_enum is_active = UVM_ACTIVE);
  master_config = apb_master_config::type_id::create("master_config");
  master_config.name = name;
  master_config.is_active = is_active;
endfunction : add_master

// apb_config - Returns the slave psel index
function int apb_config::get_slave_psel_by_addr(int addr);
  for (int i = 0; i < slave_configs.size(); i++)
    if(slave_configs[i].check_address_range(addr)) begin
      return slave_configs[i].psel_index;
    end
endfunction : get_slave_psel_by_addr

// apb_config - Return the name of the slave
function string apb_config::get_slave_name_by_addr(int addr);
  for (int i = 0; i < slave_configs.size(); i++)
    if(slave_configs[i].check_address_range(addr)) begin
      return slave_configs[i].name;
    end
endfunction : get_slave_name_by_addr

//================================================================
// Default APB configuration - One Master, Two slaves
//================================================================
class default_apb_config extends apb_config;

  `uvm_object_utils(default_apb_config)

  function new(string name = "default_apb_config-S0S1-master");
    super.new(name);
    add_slave("slave0", 32'h0000_0000, 32'h7FFF_FFFF, 0, UVM_ACTIVE);
    add_slave("slave1", 32'h8000_0000, 32'hFFFF_FFFF, 1, UVM_ACTIVE);
    add_master("master", UVM_ACTIVE);
  endfunction

endclass : default_apb_config

`endif // APB_CONFIG_SV
