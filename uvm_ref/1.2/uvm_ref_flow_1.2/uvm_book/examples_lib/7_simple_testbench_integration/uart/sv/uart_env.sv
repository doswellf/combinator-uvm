/*-------------------------------------------------------------------------
File name   : uart_env.sv
Title       : UART UVC env file 
Project     :
Created     :
Description : Creates and configures the UART UVC
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


`ifndef UART_ENV_SVH
`define UART_ENV_SVH

class uart_env extends uvm_env;

  // Virtual Interface variable
  virtual interface uart_if vif;

  // Environment Configuration Paramters
  uart_config cfg;         // UART configuration object
  bit checks_enable = 1;
  bit coverage_enable = 1;
   
  // Components of the environment
  uart_tx_agent Tx;
  uart_rx_agent Rx;

  // Used to update the config when it is updated during simulation
  uvm_analysis_imp#(uart_config, uart_env) dut_cfg_port_in;

  // This macro provide implementation of get_type_name() and create()
  `uvm_component_utils_begin(uart_env)
    `uvm_field_object(cfg, UVM_DEFAULT)
    `uvm_field_int(checks_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_component_utils_end

  // Constructor - required UVM syntax
  function new( string name, uvm_component parent);
    super.new(name, parent);
    dut_cfg_port_in = new("dut_cfg_port_in", this);
  endfunction

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task update_vif_enables();
  extern virtual function void write(uart_config cfg);
  extern virtual function void update_config(uart_config cfg);

endclass : uart_env

//UVM build_phase
function void uart_env::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Configure
  if ( cfg == null)
    if (!uvm_config_db#(uart_config)::get(this, "", "cfg", cfg)) begin
      `uvm_info("NOCONFIG", "No uart_config, creating...", UVM_MEDIUM)
      cfg = uart_config::type_id::create("cfg", this);
      if (!cfg.randomize())
         `uvm_error("RNDFAIL", "Could not randomize uart_config using default values")
      `uvm_info(get_type_name(), {"Printing cfg:\n", cfg.sprint()}, UVM_MEDIUM)
    end
  // Configure the sub-components
  uvm_config_object::set(this, "Tx*", "cfg", cfg);
  uvm_config_object::set(this, "Rx*", "cfg", cfg);

  // Create sub-components
  Tx = uart_tx_agent::type_id::create("Tx",this);
  Rx = uart_rx_agent::type_id::create("Rx",this);
endfunction : build_phase

//UVM connect_phase
function void uart_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // Get the agent's virtual interface if set via config
  if(!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
    `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
endfunction : connect_phase

// Function to assign the checks and coverage enable bits
task uart_env::update_vif_enables();
  // Make assignments at time 0 based on configuration
  vif.has_checks <= checks_enable;
  vif.has_coverage <= coverage_enable;
  forever begin
    @(checks_enable or coverage_enable);
    vif.has_checks <= checks_enable;
    vif.has_coverage <= coverage_enable;
  end
endtask : update_vif_enables

// UVM run_phase
task uart_env::run_phase(uvm_phase phase);
  fork 
    update_vif_enables(); 
  join
endtask : run_phase
  
// Update the config when RGM updates?
function void uart_env::write(input uart_config cfg );
  this.cfg = cfg;
  update_config(cfg);
endfunction : write

// Update Agent config when config updates
function void uart_env::update_config(input uart_config cfg );
  Tx.update_config(cfg);
  Rx.update_config(cfg);   
endfunction : update_config

`endif
