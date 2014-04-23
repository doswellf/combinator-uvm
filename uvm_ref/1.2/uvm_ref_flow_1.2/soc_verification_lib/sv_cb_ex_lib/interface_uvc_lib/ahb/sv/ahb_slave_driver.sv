// IVB checksum: 519799952
/*-----------------------------------------------------------------
File name     : ahb_slave_driver.sv
Created       : Wed May 19 15:42:21 2010
Description   : This file implements the slave driver functionality
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


`ifndef AHB_SLAVE_DRIVER_SV
`define AHB_SLAVE_DRIVER_SV

//------------------------------------------------------------------------------
//
// CLASS: ahb_slave_driver
//
//------------------------------------------------------------------------------

  /***************************************************************************
   IVB-NOTE : REQUIRED : slave DRIVER functionality : DRIVER
   -------------------------------------------------------------------------
   Modify the following methods to match your protocol:
     o respond_transfer() - response driving
     o reset_signals() - slave signals reset values
   Note that if you change/add signals to the physical interface, you must
   also change these methods.
   ***************************************************************************/

class ahb_slave_driver extends uvm_driver #(ahb_transfer);

  // The virtual interface used to drive and view HDL signals.
  virtual interface ahb_if vif;
    
  // Count transfer_responses sent
  int num_sent;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils(ahb_slave_driver)

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual protected task get_and_drive();
  extern virtual protected task reset_signals();
  extern virtual protected task send_response(ahb_transfer response);
  extern virtual function void report();

endclass : ahb_slave_driver

//UVM connect_phase
function void ahb_slave_driver::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
endfunction : connect_phase

  // UVM run() phase
  task ahb_slave_driver::run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
    join
  endtask : run_phase

  // Continually detects transfers
  task ahb_slave_driver::get_and_drive();
    @(posedge vif.ahb_resetn);
    `uvm_info(get_type_name(), "Reset dropped", UVM_MEDIUM)
    forever begin
      @(posedge vif.ahb_clock iff vif.AHB_HREADY===1'b1);
      // Get new item from the sequencer
      seq_item_port.get_next_item(rsp);
      // Drive the response
      send_response(rsp);
      // Communicate item done to the sequencer
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  // Reset all signals
  task ahb_slave_driver::reset_signals();
    forever begin
      @(negedge vif.ahb_resetn);
      `uvm_info(get_type_name(), "Reset observed", UVM_MEDIUM)
      vif.AHB_HREADY      <= 0;
    end
  endtask : reset_signals

  // Response to a transfer from the DUT
  task ahb_slave_driver::send_response(ahb_transfer response);
    `uvm_info(get_type_name(),
      $sformatf("Driving response :\n%s",rsp.sprint()), UVM_HIGH)
    response.data = vif.AHB_HWDATA;
    vif.AHB_HREADY  <= 1;
    @(posedge vif.ahb_clock);
    vif.AHB_HREADY <= 0;
    @(posedge vif.ahb_clock);
    num_sent++;
  endtask : send_response

  // UVM report() phase
  function void ahb_slave_driver::report();
    `uvm_info(get_type_name(),
      $sformatf("\nReport: AHB slave driver sent %0d transfer responses",
      num_sent), UVM_LOW)
  endfunction : report

`endif // AHB_SLAVE_DRIVER_SV

