/****************************************************************
  File: apb_bus_monitor.sv
  Description: APB Bus Monitor
****************************************************************/
`ifndef APB_BUS_MONITOR_SV
`define APB_BUS_MONITOR_SV
//------------------------------------------------------------------------------
// CLASS: apb_bus_monitor
//------------------------------------------------------------------------------

class apb_bus_monitor extends uvm_monitor;

  // The virtual interface used to view HDL signals.
  virtual apb_if vif;

  // The following two bits are used to control whether checks and coverage are
  // done both in the monitor class and the interface.
  bit checks_enable = 1; 
  bit coverage_enable = 1;

  //APB Configuration Class
  apb_config cfg;

  // TLM PORT for sending transaction OUT to scoreboard, register database, etc
  uvm_analysis_port #(apb_transfer) item_collected_port;

  // The current apb_transfer
  protected apb_transfer trans_collected;

  // Property indicating the number of transactions occuring on the apb.
  int unsigned num_transactions = 0;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_bus_monitor)
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
  endfunction : new

  // Additional class methods
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern protected function void perform_checks();
  extern virtual protected function void perform_coverage();
  extern virtual function void report_phase(uvm_phase phase);

endclass : apb_bus_monitor

// UVM connect_phase
function void apb_bus_monitor::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual apb_if)::get(this, get_full_name(), "vif", vif))
    `uvm_error("NOVIF", {"virtual interface (apb_if) must be set for: ", get_full_name(), ".vif"})
endfunction : connect_phase

// UVM run_phase
task apb_bus_monitor::run_phase(uvm_phase phase);
  apb_transfer trans_collected;
  trans_collected = apb_transfer::type_id::create("trans_collected");
  forever begin
    @(posedge vif.pclk iff (vif.psel != 0));
    void'(this.begin_tr(trans_collected));
    trans_collected.addr = vif.paddr;
    case (vif.pwrite)
      1'b0 : trans_collected.direction = APB_READ;
      1'b1 : trans_collected.direction = APB_WRITE;
    endcase
    if(trans_collected.direction == APB_READ)
      trans_collected.data = vif.prdata;
    if (trans_collected.direction == APB_WRITE)
      trans_collected.data = vif.pwdata;
    @(posedge vif.pclk);
    if(trans_collected.direction == APB_READ)
      trans_collected.data = vif.prdata;
    this.end_tr(trans_collected);
    if (coverage_enable) perform_coverage();
    if (coverage_enable) perform_checks();
    item_collected_port.write(trans_collected);
    `uvm_info(get_type_name(), $sformatf("Transfer collected :\n%s",
              trans_collected.sprint()), UVM_HIGH)
     num_transactions++;
    end
endtask : run_phase

// FUNCTION: perform_checks()
function void apb_bus_monitor::perform_checks();
  // Add checks here
endfunction : perform_checks

// FUNCTION : perform_coverage()
function void apb_bus_monitor::perform_coverage();
  apb_transfer_cg.sample();
endfunction : perform_coverage

// FUNCTION: UVM report_phase
function void apb_bus_monitor::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Report: APB monitor collected %0d transfers", num_transactions), UVM_LOW);
endfunction : report_phase

`endif // APB_BUS_MONITOR_SV
