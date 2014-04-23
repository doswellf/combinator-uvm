/****************************************************************
  Example 5-11: APB Monitor

  To run:   %  irun -uvm ex5-11_apb_monitor.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-11_apb_monitor.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_transfer.sv"

//------------------------------------------------------------------------------
// CLASS: apb_monitor
//------------------------------------------------------------------------------

class apb_monitor extends uvm_monitor;

  // The following two bits are used to control whether checks and coverage are
  // done both in the monitor class and the interface.
  bit checks_enable = 1; 
  bit coverage_enable = 1;

  // TLM PORT for sending transaction OUT to scoreboard, register database, etc
  uvm_analysis_port #(apb_transfer) item_collected_port;

  // TLM Connection to the Collector - look for a write() task implementation
  uvm_analysis_imp  #(apb_transfer, apb_monitor) coll_mon_port;

  // The current apb_transfer
  protected apb_transfer trans_collected;

  // Property indicating the number of transactions occuring on the apb.
  int unsigned num_transactions = 0;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_monitor)
    `uvm_field_int(checks_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_component_utils_end

  covergroup apb_transfer_cg;
    TRANS_ADDR : coverpoint trans_collected.addr {
      bins ZERO = {0};
      bins NON_ZERO = {[1:8'h7f]};
    }
    TRANS_DIRECTION : coverpoint trans_collected.direction;
    TRANS_DATA : coverpoint trans_collected.data {
      bins ZERO     = {0};
      bins NON_ZERO = {[1:8'hfe]};
      bins ALL_ONES = {8'hff};
    }
    TRANS_ADDR_X_TRANS_DIRECTION: cross TRANS_ADDR, TRANS_DIRECTION;
  endgroup

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
    trans_collected = new();
    apb_transfer_cg = new();
    // Create TLM ports
    item_collected_port = new("item_collected_port", this);
    coll_mon_port = new("coll_mon_port", this);
  endfunction : new

  // Additional class methods
  extern virtual function void write(apb_transfer trans);
  extern protected function void perform_checks();
  extern virtual protected function void perform_coverage();
  extern virtual function void report_phase(uvm_phase phase);

endclass : apb_monitor

// FUNCTION: write - transaction interface to the collector
function void apb_monitor::write(apb_transfer trans);
  // Make a copy of the transaction (may not be necessary!)
  $cast(trans_collected, trans.clone());
  num_transactions++;  
  `uvm_info(get_type_name(), {"Transaction Collected:\n", trans_collected.sprint()}, UVM_HIGH)
  if (checks_enable) perform_checks();
  if (coverage_enable) perform_coverage();
  // Broadcast transaction to the rest of the environment (module UVC)
  item_collected_port.write(trans_collected);
endfunction : write

// FUNCTION: perform_checks()
function void apb_monitor::perform_checks();
  // Add checks here
endfunction : perform_checks

// FUNCTION : perform_coverage()
function void apb_monitor::perform_coverage();
  apb_transfer_cg.sample();
endfunction : perform_coverage

// FUNCTION: UVM report_phase
function void apb_monitor::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Report: APB monitor collected %0d transfers", num_transactions), UVM_LOW);
endfunction : report_phase
