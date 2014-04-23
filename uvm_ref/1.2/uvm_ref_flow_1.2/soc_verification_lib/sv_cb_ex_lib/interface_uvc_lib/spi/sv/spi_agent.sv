/*-------------------------------------------------------------------------
File name   : spi_agent.sv
Title       : SPI SystemVerilog UVM UVC
Project     : UVM SystemVerilog Cluster Level Verification
Created     :
Description : 
Notes       :  
---------------------------------------------------------------------------*/
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


`ifndef SPI_AGENT_SV
`define SPI_AGENT_SV

class spi_agent extends uvm_agent;

  uvm_active_passive_enum is_active = UVM_ACTIVE;
  int agent_id;

  spi_driver driver;
  spi_sequencer sequencer;
  spi_monitor monitor;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(spi_agent)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
    `uvm_field_int(agent_id, UVM_ALL_ON)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // build
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    monitor = spi_monitor::type_id::create("monitor", this);
    if(is_active == UVM_ACTIVE) begin
      sequencer = spi_sequencer::type_id::create("sequencer", this);
      driver = spi_driver::type_id::create("driver", this);
      driver.monitor = monitor;
    end
  endfunction : build_phase

  // connect
  function void connect_phase(uvm_phase phase);
    if(is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction : connect_phase

  // assign csr of the agent's cheldren
  function void assign_csr(spi_csr_s csr_s);
    monitor.csr_s = csr_s;
    if (is_active == UVM_ACTIVE) begin
      driver.csr_s = csr_s;
    end
  endfunction : assign_csr

endclass : spi_agent

`endif // SPI_AGENT_SV

