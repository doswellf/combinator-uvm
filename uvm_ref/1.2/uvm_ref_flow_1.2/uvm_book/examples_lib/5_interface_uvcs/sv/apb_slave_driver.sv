/*******************************************************************************
  Copyright (c) 2006 Cadence Design Systems, Inc.
  All rights reserved worldwide.
********************************************************************************
  FILE : apb_slave_driver.sv
*******************************************************************************/

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

// Get the vif as a config property
function void apb_slave_driver::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // The virtual interface is required for this UVC to operate. It may have
  // been set via the configuration property, or it may have been set directly
  // by its containing agent.
  if(vif == null) begin
    if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
      `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
  end
endfunction : connect_phase

// Declaration of the run_phase() phase method.  This method
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
  @(posedge vif.presetn);
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
    @(negedge vif.presetn);
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
    @(posedge vif.pclk);
    vif.prdata <= 32'hzzzz_zzzz;
  end
endtask : respond_to_transfer

`endif // APB_SLAVE_DRIVER_SV
