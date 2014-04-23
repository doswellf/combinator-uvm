/*******************************************************************************
  FILE : apb_master_driver.sv
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


`ifndef APB_MASTER_DRIVER_SV
`define APB_MASTER_DRIVER_SV

//------------------------------------------------------------------------------
// CLASS: apb_master_driver declaration
//------------------------------------------------------------------------------

class apb_master_driver extends uvm_driver #(apb_transfer);

  // The virtual interface used to drive and view HDL signals.
  virtual apb_if vif;
  
  // A pointer to the configuration unit of the agent
  apb_config cfg;
  
  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_master_driver)
    `uvm_field_object(cfg, UVM_DEFAULT|UVM_REFERENCE)
  `uvm_component_utils_end

  // Constructor which calls super.new() with appropriate parameters.
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual protected task get_and_drive();
  extern virtual protected task reset();
  extern virtual protected task drive_transfer (apb_transfer trans);
  extern virtual protected task drive_address_phase (apb_transfer trans);
  extern virtual protected task drive_data_phase (apb_transfer trans);

endclass : apb_master_driver

// UVM build_phase
function void apb_master_driver::build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg == null)
      if (!uvm_config_db#(apb_config)::get(this, "", "cfg", cfg))
      `uvm_error("NOCONFIG", "apb_config not set for this component")
endfunction : build_phase

// UVM connect_phase - gets the vif as a config property
function void apb_master_driver::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
    `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
endfunction : connect_phase

// Declaration of the UVM run_phase method.
task apb_master_driver::run_phase(uvm_phase phase);
  get_and_drive();
endtask : run_phase

// This task manages the interaction between the sequencer and driver
task apb_master_driver::get_and_drive();
  while (1) begin
    reset();
    fork 
      @(negedge vif.preset)
        // APB_MASTER_DRIVER tag required for Debug Labs
        `uvm_info("APB_MASTER_DRIVER", "get_and_drive: Reset dropped", UVM_MEDIUM)
      begin
        // This thread will be killed at reset
        forever begin
          @(posedge vif.pclock iff (vif.preset))
          seq_item_port.get_next_item(req);
          $cast(rsp, req.clone());
          rsp.set_id_info(req);
          drive_transfer(rsp);
          // KATHLEEN MODIFIED 3/26/2012 
          //seq_item_port.item_done(req);
          seq_item_port.item_done();
          // KATHLEEN ADDED 4/2/2012 
          seq_item_port.put_response(rsp);
        end
      end
      join_any
      disable fork;
      //If we are in the middle of a transfer, need to end the tx. Also,
      //do any reset cleanup here. The only way we got to this point is via
      //a reset.
      if(req.is_active()) this.end_tr(req);
  end
endtask : get_and_drive

// Drive all signals to reset state 
task apb_master_driver::reset();
  // If the reset is not active, then wait for it to become active before
  // resetting the interface.
  wait(!vif.preset);
  // APB_MASTER_DRIVER tag required for Debug Labs
  `uvm_info("APB_MASTER_DRIVER", $sformatf("Reset observed"), UVM_MEDIUM)
  vif.paddr     <= 'h0;
  vif.pwdata    <= 'h0;
  vif.prwd      <= 'b0;
  vif.psel      <= 'b0;
  vif.penable   <= 'b0;
endtask : reset

// Drives a transfer when an item is ready to be sent.
task apb_master_driver::drive_transfer (apb_transfer trans);
  void'(this.begin_tr(trans, "apb master driver", "UVM Debug",
       "APB master driver transaction from get_and_drive"));
  if (trans.transmit_delay > 0) begin
    repeat(trans.transmit_delay) @(posedge vif.pclock);
  end
  drive_address_phase(trans);
  drive_data_phase(trans);
  // APB_MASTER_DRIVER_TR tag required for Debug Labs
  `uvm_info("APB_MASTER_DRIVER_TR", $sformatf("APB Finished Driving Transfer \n%s",
            trans.sprint()), UVM_HIGH)
  this.end_tr(trans);
endtask : drive_transfer

// Drive the address phase of the transfer
task apb_master_driver::drive_address_phase (apb_transfer trans);
  int slave_indx;
  slave_indx = cfg.get_slave_psel_by_addr(trans.addr);
  vif.paddr <= trans.addr;
  vif.psel <= (1<<slave_indx);
  vif.penable <= 0;
  if (trans.direction == APB_READ) begin
    vif.prwd <= 1'b0;
  end    
  else begin
    vif.prwd <= 1'b1;
    vif.pwdata <= trans.data;
  end
  @(posedge vif.pclock);
endtask : drive_address_phase

// Drive the data phase of the transfer
task apb_master_driver::drive_data_phase (apb_transfer trans);
  vif.penable <= 1;
  @(posedge vif.pclock iff vif.pready); 
  if (trans.direction == APB_READ) begin
    trans.data = vif.prdata;
  end
  vif.penable <= 0;
  vif.psel    <= 0;
//KATHLEEN ADDED THIS - DRIVER WAS RETURNING TOO SOON
  @(posedge vif.pclock);
endtask : drive_data_phase

`endif // APB_MASTER_DRIVER_SV
