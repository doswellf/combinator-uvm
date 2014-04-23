/****************************************************************
  File: apb_monitor.sv
  Description: APB Monitor
****************************************************************/
`ifndef APB_MONITOR_SV
`define APB_MONITOR_SV
//------------------------------------------------------------------------------
// CLASS: apb_monitor
//------------------------------------------------------------------------------

class apb_monitor extends uvm_monitor;

  // APB Configuration Class
  apb_config cfg;

  // The following two bits are used to control whether checks and coverage are
  // done both in the monitor class and the interface.
  bit checks_enable = 1; 
  bit coverage_enable = 1;

  // TLM PORT for sending transaction OUT to scoreboard, register database, etc
  uvm_analysis_port #(apb_transfer) item_collected_port;

  // TLM Connection to the Collector - look for a write() task implementation
  uvm_analysis_imp  #(apb_transfer, apb_monitor) coll_mon_port;

  // Allows the sequencer to look at monitored data for responses
  uvm_blocking_peek_imp#(apb_transfer,apb_monitor) addr_trans_export;

  // Allows monitor to look at collector for address information
  uvm_blocking_peek_port#(apb_transfer) addr_trans_port;

  event trans_addr_grabbed;

  // The current apb_transfer
  protected apb_transfer trans_collected;

  // Property indicating the number of transactions occuring on the apb.
  int unsigned num_transactions = 0;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_monitor)
    `uvm_field_object(cfg, UVM_DEFAULT|UVM_REFERENCE)
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
    addr_trans_export = new("addr_trans_export", this);
    addr_trans_port   = new("addr_trans_port", this);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern task peek (output apb_transfer trans);
  extern virtual function void write(apb_transfer trans);
  extern protected function void perform_checks();
  extern virtual protected function void perform_coverage();
  extern virtual function void report_phase(uvm_phase phase);

endclass : apb_monitor

// UVM build_phase
function void apb_monitor::build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg == null)
      if (!uvm_config_db#(apb_config)::get(this, "", "cfg", cfg))
      `uvm_warning("NOCONFIG", "apb_config not set for this component")
endfunction : build_phase

// UVM run_phase
task apb_monitor::run_phase(uvm_phase phase);
  forever begin
    addr_trans_port.peek(trans_collected);
    `uvm_info(get_type_name(), $sformatf("Address Phase Complete: %h[%s]", trans_collected.addr, trans_collected.direction.name() ), UVM_HIGH)
    -> trans_addr_grabbed;
  end
endtask : run_phase

// TASK: peek - Allows the sequencer to peek at monitor for responses
task apb_monitor::peek(output apb_transfer trans);
  @trans_addr_grabbed;
  trans = trans_collected;
endtask

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

// FUNCTION: UVM report_phase()
function void apb_monitor::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Report: APB monitor collected %0d transfers", num_transactions), UVM_LOW);
endfunction : report_phase

`endif // APB_MONITOR_SV
