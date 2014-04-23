/*******************************************************************************
  FILE : apb_slave_driver.sv
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


`ifndef APB_SLAVE_DRIVER_SV
`define APB_SLAVE_DRIVER_SV

//------------------------------------------------------------------------------
// CLASS: apb_slave_driver declaration
//------------------------------------------------------------------------------

class apb_slave_driver extends uvm_driver #(apb_transfer);

  // The virtual interface used to drive and view HDL signals.
  virtual apb_if vif;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils(apb_slave_driver)

  // Constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task get_and_drive();
  extern virtual task reset_signals();
  extern virtual task respond_to_transfer(apb_transfer resp);

endclass : apb_slave_driver

// UVM connect_phase - gets the vif as a config property
function void apb_slave_driver::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
    if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
      `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
endfunction : connect_phase

// Externed virtual declaration of the run_phase method.  This method
// fork/join_none's the get_and_drive() and reset_signals() methods.
task apb_slave_driver::run_phase(uvm_phase phase);
  fork
    get_and_drive();
    reset_signals();
  join
endtask : run_phase

// Function that manages the interaction between the slave
// sequence sequencer and this slave driver.
task apb_slave_driver::get_and_drive();
  @(posedge vif.preset);
  `uvm_info(get_type_name(), "Reset dropped", UVM_MEDIUM)
  forever begin
    seq_item_port.get_next_item(req);
    respond_to_transfer(req);
    seq_item_port.item_done();
  end
endtask : get_and_drive

// Process task that assigns signals to reset state when reset signal set
task apb_slave_driver::reset_signals();
  forever begin
    @(negedge vif.preset);
    `uvm_info(get_type_name(), "Reset observed",  UVM_MEDIUM)
    vif.prdata <= 32'hzzzz_zzzz;
    vif.pready <= 0;
    vif.pslverr <= 0;
  end
endtask : reset_signals

  // This task drives the response phases of a transfer.
task apb_slave_driver::respond_to_transfer(apb_transfer resp);
  begin
    vif.pready <= 1'b1;
    if (resp.direction == APB_READ)
      vif.prdata <= resp.data;
    @(posedge vif.pclock);
    vif.prdata <= 32'hzzzz_zzzz;
  end
endtask : respond_to_transfer

`endif // APB_SLAVE_DRIVER_SV
