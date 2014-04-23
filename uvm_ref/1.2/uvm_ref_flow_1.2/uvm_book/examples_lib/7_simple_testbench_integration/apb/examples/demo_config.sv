/*******************************************************************************
  Copyright (c) 2006 Cadence Design Systems, Inc.
  All rights reserved worldwide.
********************************************************************************
  FILE : demo_config.sv
*******************************************************************************/

/*
// APB Slave Configuration Information
class apb_slave_config extends uvm_object;
  string name;
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  int start_address;
  int end_address;
  int psel_index;
endclass

// APB Master Configuration Information
class apb_master_config extends uvm_object;
  string name;
  uvm_active_passive_enum is_active = UVM_ACTIVE;
endclass

// APB Configuration Information 
class apb_config extends uvm_object;
  // APB has one master and N slaves
  apb_master_config master_config;
  apb_slave_config slave_configs[$];
  extern function void add_slave(string name, int start_addr, int end_addr,
              int psel_indx, uvm_active_passive_enum is_active = UVM_ACTIVE);
  extern function void add_master(string name,
              uvm_active_passive_enum is_active = UVM_ACTIVE);
  extern function int get_slave_psel_by_addr(int addr);
  extern function string get_slave_name_by_addr(int addr);
endclass : apb_config
*/

class demo_config extends apb_config;

  `uvm_object_utils(demo_config)

  function new(string name = "demo_config");
    super.new(name);
    add_slave("slave0", 32'h0000_0000, 32'hFFFF_FFFF, 0, UVM_ACTIVE);
    add_slave("slave1", 32'h0000_0000, 32'h7FFF_FFFF, 1, UVM_PASSIVE);
    add_master("master", UVM_ACTIVE);
  endfunction

endclass

class demo_048_config extends apb_config;

  `uvm_object_utils(demo_048_config)

  function new(string name = "demo_048_config");
    super.new(name);
    add_slave("slave0", 32'h0001_0000, 32'h7FFF_FFFF, 0, UVM_ACTIVE);
    add_slave("slave1", 32'h8000_0000, 32'hFFFF_FFFF, 4, UVM_ACTIVE);
    add_slave("slave2", 32'h0000_0000, 32'h0000_FFFF, 8, UVM_ACTIVE);
    //add_slave("slave0", 32'h0000_0000, 32'hFFFF_FFFF, 0, UVM_ACTIVE);
    //add_slave("slave1", 32'h0000_0000, 32'h7FFF_FFFF, 1, UVM_PASSIVE);
    add_master("master", UVM_ACTIVE);
  endfunction

endclass
