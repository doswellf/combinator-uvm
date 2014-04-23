// IVB checksum: 223843813
/*-----------------------------------------------------------------
File name     : ahb_slave_monitor.sv
Created       : Wed May 19 15:42:21 2010
Description   : This file implements the slave monitor.
              : The slave monitor monitors the activity of
              : its interface bus.
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


`ifndef AHB_SLAVE_MONITOR_SV
`define AHB_SLAVE_MONITOR_SV

//------------------------------------------------------------------------------
//
// CLASS: ahb_slave_monitor
//
//------------------------------------------------------------------------------

class ahb_slave_monitor extends uvm_monitor;
  
  // The virtual interface needed for this component to drive
  // and view HDL signals.
  virtual interface ahb_if vif;

  // Property indicating the number of transactions occuring on the ahb.
  protected int unsigned num_transactions = 0;

  // Count transfer responses collected
  int num_col;

  // The following two bits are used to control whether checks and coverage are
  // done in the monitor
  bit checks_enable = 1;
  bit coverage_enable = 1;
  
  // This TLM port is used to connect the monitor to the scoreboard
  uvm_analysis_port#(ahb_transfer) item_collected_port;

  // TLM Connection to the Collector - look for a write() task implementation
  uvm_analysis_imp  #(ahb_transfer, ahb_slave_monitor) coll_mon_port;

   event transaction_ended;
  
  // Current monitored transfer 
  protected ahb_transfer transfer;
 
  // Covergroup for transfer
  covergroup slave_transfer_cg;
    option.per_instance = 1;
    direction: coverpoint transfer.direction;
  endgroup : slave_transfer_cg

  // Provide UVM automation and utility methods
  `uvm_component_utils_begin(ahb_slave_monitor)
    `uvm_field_int(checks_enable, UVM_ALL_ON)
    `uvm_field_int(coverage_enable, UVM_ALL_ON)
  `uvm_component_utils_end

  // Constructor - required syntax for UVM automation and utilities
  function new(string name, uvm_component parent);
    super.new(name, parent);
    // Create the covergroup
    slave_transfer_cg = new();
    slave_transfer_cg.set_inst_name("slave_transfer_cg");
    // Create the TLM port
    item_collected_port = new("item_collected_port", this);
    coll_mon_port = new("coll_mon_port", this);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  //Receives transfer from the collector
  extern virtual function void write(ahb_transfer trans); 
  extern virtual protected function void perform_checks();
  extern virtual protected function void perform_coverage();
  extern virtual function void report();

endclass : ahb_slave_monitor

// UVM build_phase
function void ahb_slave_monitor::build_phase(uvm_phase phase);
    super.build_phase(phase);
endfunction : build_phase

// FUNCTION: write - transaction interface to the collector
function void ahb_slave_monitor::write(ahb_transfer trans);
  // Make a copy of the transaction (may not be necessary!)
  $cast(transfer, trans.clone());
  num_transactions++;  
  `uvm_info(get_type_name(), {"Transaction Collected:\n", transfer.sprint()}, UVM_HIGH)
   if (checks_enable) perform_checks();
   if (coverage_enable) perform_coverage();
  // Broadcast transaction to the rest of the environment (module UVC)
  item_collected_port.write(transfer);
  -> transaction_ended;
endfunction : write

  /***************************************************************************
  IVB-NOTE : OPTIONAL : slave Monitor Protocol Checks : Checks
  -------------------------------------------------------------------------
  Add protocol checks within the perform_checks() method. 
  ***************************************************************************/
  // perform__checks
  function void ahb_slave_monitor::perform_checks();
    // Add checks here
  endfunction : perform_checks
  
 /***************************************************************************
  IVB-NOTE : OPTIONAL : slave Monitor Coverage : Coverage
  -------------------------------------------------------------------------
  Modify the slave_transfer_cg coverage group to match your protocol.
  Add new coverage groups, and edit the perform_coverage() method to sample them
  ***************************************************************************/

  // Triggers coverage events
  function void ahb_slave_monitor::perform_coverage();
    slave_transfer_cg.sample();
  endfunction : perform_coverage

  // UVM report() phase
  function void ahb_slave_monitor::report();
    `uvm_info(get_type_name(), 
      $sformatf("\nReport: AHB slave monitor collected %0d transfer responses",
      num_col), UVM_LOW)
  endfunction : report

`endif // AHB_SLAVE_MONITOR_SV

