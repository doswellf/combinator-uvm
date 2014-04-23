/*******************************************************************************
  FILE : apb_slave_agent.sv
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


`ifndef APB_SLAVE_AGENT_SV
`define APB_SLAVE_AGENT_SV

//------------------------------------------------------------------------------
// CLASS: apb_slave_agent
//------------------------------------------------------------------------------

class apb_slave_agent extends uvm_agent;

  // Virtual interface for this set components. The virtual interface can
  // be set from the agent, or set via config to each component.
  virtual apb_if vif;

  // This field determines whether an agent is active or passive.
  //uvm_active_passive_enum is_active = UVM_ACTIVE;

  // Slave Configuration Information:  name, is_active, psel_index,
  //                                   start_address, end_address
  apb_slave_config cfg;

  apb_slave_driver    driver;
  apb_slave_sequencer sequencer;
  apb_monitor   monitor;
  apb_collector collector;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_slave_agent)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
    `uvm_field_object(cfg, UVM_DEFAULT | UVM_REFERENCE)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void update_config(input apb_slave_config cfg);
endclass : apb_slave_agent

// UVM build_phase
function void apb_slave_agent::build_phase(uvm_phase phase);
  uvm_object config_obj;
  super.build_phase(phase);
  // Get the configuration information for this component
  if (cfg == null) begin
    if (!uvm_config_db#(apb_slave_config)::get(this, "", "cfg", cfg))
     `uvm_warning("NOCONFIG",
         "Config not set for slave agent using default is_active")
    end
  else is_active = cfg.is_active;
  monitor = apb_monitor::type_id::create("monitor",this);
  collector = apb_collector::type_id::create("collector",this);
  // Create the sequencer and driver only if ACTIVE
  if (is_active == UVM_ACTIVE) begin
    sequencer = apb_slave_sequencer::type_id::create("sequencer",this);
    driver = apb_slave_driver::type_id::create("driver",this);
  end
endfunction : build_phase

// update_config() 
function void apb_slave_agent::update_config(input apb_slave_config cfg);
  if (is_active == UVM_ACTIVE) begin
    sequencer.cfg = cfg;
  end
endfunction : update_config

// UVM connect_phase
function void apb_slave_agent::connect_phase(uvm_phase phase);
  // Get the agents virtual interface if set via get_config
  if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
    `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
  // If the vif was set to the agent, apply it to its children
  uvm_config_db#(virtual apb_if)::set(this, "*", "vif", vif);

  collector.item_collected_port.connect(monitor.coll_mon_port);
  monitor.addr_trans_port.connect(collector.addr_trans_export);
  if (is_active == UVM_ACTIVE) begin
    // Connect the driver to the sequencer using TLM interface
    driver.seq_item_port.connect(sequencer.seq_item_export);
  end
endfunction : connect_phase

`endif // APB_SLAVE_AGENT_SV
