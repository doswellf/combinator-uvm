// IVB checksum: 2064975656
/*-----------------------------------------------------------------
File name     : ahb_env.sv
Created       : Wed May 19 15:42:20 2010
Description   : This file implements the OVC env.
Notes         :
-----------------------------------------------------------------*/
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


`ifndef AHB_ENV_SV
`define AHB_ENV_SV

//------------------------------------------------------------------------------
//
// CLASS: ahb_env
//
//------------------------------------------------------------------------------

class ahb_env extends uvm_env;

  // Virtual Interface variable
  protected virtual interface ahb_if vif;
 
  // The following two bits are used to control whether checks and coverage are
  // done both in the bus monitor class and the interface.
  bit checks_enable = 1; 
  bit coverage_enable = 1;

  // Components of the environment
  ahb_master_agent master_agent;
  ahb_slave_agent slave_agent;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(ahb_env)
    `uvm_field_int(checks_enable, UVM_ALL_ON)
    `uvm_field_int(coverage_enable, UVM_ALL_ON)
  `uvm_component_utils_end

  // Constructor - required syntax for UVM automation and utilities
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern protected task update_vif_enables();
  extern virtual task run_phase(uvm_phase phase);

endclass : ahb_env

  // UVM build() phase
  function void ahb_env::build_phase(uvm_phase phase);
    super.build_phase(phase);
    master_agent = ahb_master_agent::type_id::create("master_agent", this);
  endfunction : build_phase

//UVM connect_phase
function void ahb_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
   `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
endfunction : connect_phase

  // Function to assign the checks and coverage bits
  task ahb_env::update_vif_enables();
    // Make assignments at time zero based upon config
    vif.has_checks <= checks_enable;
    vif.has_coverage <= coverage_enable;
    forever begin
      // Make assignments whenever enables change after time zero
      @(checks_enable || coverage_enable);
      vif.has_checks <= checks_enable;
      vif.has_coverage <= coverage_enable;
    end
  endtask : update_vif_enables

  // UVM run() phase
  task ahb_env::run_phase(uvm_phase phase);
    fork
      update_vif_enables();
    join_none
  endtask

`endif // AHB_ENV_SV

