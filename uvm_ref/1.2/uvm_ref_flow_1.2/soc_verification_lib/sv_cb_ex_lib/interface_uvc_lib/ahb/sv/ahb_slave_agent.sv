// IVB checksum: 1298481799
/*-----------------------------------------------------------------
File name     : ahb_slave_agent.sv
Created       : Wed May 19 15:42:21 2010
Description   : This file implements the slave agent
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


`ifndef AHB_SLAVE_AGENT_SV
`define AHB_SLAVE_AGENT_SV

//------------------------------------------------------------------------------
//
// CLASS: ahb_slave_agent
//
//------------------------------------------------------------------------------

class ahb_slave_agent extends uvm_agent;
 
  // This field determines whether an agent is active or passive.
  protected uvm_active_passive_enum is_active = UVM_ACTIVE;

  ahb_slave_monitor monitor;
  ahb_slave_collector collector;
  ahb_slave_sequencer sequencer;
  ahb_slave_driver driver;
  
  /***************************************************************************
   IVB-NOTE : OPTIONAL : slave Agent : Agents
   -------------------------------------------------------------------------
   Add slave fields, events, and methods.
   For each field you add:
     o Update the `uvm_component_utils_begin macro to get various UVM utilities
       for this attribute.
   ***************************************************************************/

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(ahb_slave_agent)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
  `uvm_component_utils_end

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : ahb_slave_agent

  // UVM build() phase
  function void ahb_slave_agent::build_phase(uvm_phase phase);
    super.build_phase(phase);
    monitor = ahb_slave_monitor::type_id::create("monitor", this);
    collector = ahb_slave_collector::type_id::create("collector", this);
    if(is_active == UVM_ACTIVE) begin
      sequencer = ahb_slave_sequencer::type_id::create("sequencer", this);
      driver = ahb_slave_driver::type_id::create("driver", this);
    end
  endfunction : build_phase

  // UVM connect() phase
  function void ahb_slave_agent::connect_phase(uvm_phase phase);
    collector.item_collected_port.connect(monitor.coll_mon_port);
      if(is_active == UVM_ACTIVE) begin
      // Binds the driver to the sequencer using consumer-producer interface
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction : connect_phase

`endif // AHB_SLAVE_AGENT_SV

