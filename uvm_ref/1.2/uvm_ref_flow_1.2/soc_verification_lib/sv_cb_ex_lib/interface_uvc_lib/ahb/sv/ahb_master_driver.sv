// IVB checksum: 1563143146
/*-----------------------------------------------------------------
File name     : ahb_master_driver.sv
Created       : Wed May 19 15:42:20 2010
Description   : This files implements the master driver functionality.
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


`ifndef AHB_MASTER_DRIVER_SV
`define AHB_MASTER_DRIVER_SV

//------------------------------------------------------------------------------
//
// CLASS: ahb_master_driver
//
//------------------------------------------------------------------------------

class ahb_master_driver extends uvm_driver #(ahb_transfer);

 /***************************************************************************
  IVB-NOTE : REQUIRED : master DRIVER functionality : DRIVER
  -------------------------------------------------------------------------
  Modify the following methods to match your protocol:
    o drive_transfer() - Handshake and transfer driving process
    o reset_signals() - master signal reset values
  Note that if you change/add signals to the physical interface, you must
  also change these methods.
  ***************************************************************************/

  // The virtual interface used to drive and view HDL signals.
  virtual interface ahb_if vif;
 
  // Count transfers sent
  int num_sent;

  // Provide implmentations of virtual methods such as get_type_name and create
  `uvm_component_utils(ahb_master_driver)

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual protected task get_and_drive();
  extern virtual protected task reset_signals();
  extern virtual protected task drive_transfer(ahb_transfer transfer);
  extern virtual function void report();

endclass : ahb_master_driver

//UVM connect_phase
function void ahb_master_driver::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
endfunction : connect_phase

  // UVM run() phase
  task ahb_master_driver::run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
    join
  endtask : run_phase

  // Gets transfers from the sequencer and passes them to the driver. 
  task ahb_master_driver::get_and_drive();
    @(posedge vif.ahb_resetn);
    `uvm_info(get_type_name(), "Reset dropped", UVM_MEDIUM)
    forever begin
      @(posedge vif.ahb_clock iff vif.AHB_HREADY === 1);
      // Get new item from the sequencer
      seq_item_port.get_next_item(req);
      // Drive the item
      drive_transfer(req);
      // Communicate item done to the sequencer
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  // Reset all master signals
  task ahb_master_driver::reset_signals();
    forever begin
      @(negedge vif.ahb_resetn);
      `uvm_info(get_type_name(), "Reset observed", UVM_MEDIUM)
      vif.AHB_HWDATA <= 'hz;
      vif.AHB_HTRANS <= IDLE;
    end
  endtask : reset_signals

  // Gets a transfer and drive it into the DUT
  task ahb_master_driver::drive_transfer(ahb_transfer transfer);
    @(posedge vif.ahb_clock iff vif.AHB_HREADY === 1);
        vif.AHB_HTRANS <= NONSEQ;  
        vif.AHB_HWRITE <= transfer.direction;
        vif.AHB_HSIZE <=  transfer.hsize;  
        vif.AHB_HPROT <=  transfer.prot;  
        vif.AHB_HBURST <= transfer.burst ;  
        vif.AHB_HADDR <=  transfer.address;  

    @(posedge vif.ahb_clock iff vif.AHB_HREADY === 1);
        if(transfer.direction == WRITE) 
          vif.AHB_HWDATA <= transfer.data;
        vif.AHB_HTRANS <= IDLE;  
    num_sent++;
    `uvm_info(get_type_name(), $sformatf("Item %0d Sent ...", num_sent),
      UVM_HIGH)
  endtask : drive_transfer

  // UVM report() phase
  function void ahb_master_driver::report();
    `uvm_info(get_type_name(), 
      $sformatf("\nReport: AHB master driver sent %0d transfers",
      num_sent), UVM_LOW)
  endfunction : report

`endif // AHB_MASTER_DRIVER_SV

