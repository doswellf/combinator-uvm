/****************************************************************
  Example 5-10: APB Collector

  To run:   %  irun -uvm ex5-10_apb_collector.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-10_apb_collector.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_if.sv"
`include "sv/apb_transfer.sv"

//------------------------------------------------------------------------------
// CLASS: apb_collector
//------------------------------------------------------------------------------
class apb_collector extends uvm_component;

  // The virtual interface used to view HDL signals.
  virtual apb_if vif;

  // The following two bits are used to control whether checks and coverage are
  // done both in the collector class and the interface.
  bit checks_enable = 1; 
  bit coverage_enable = 1;

  int num_transactions;

  // TLM Ports - transfer collected for monitor other components
  uvm_analysis_port #(apb_transfer) item_collected_port;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_collector)
    `uvm_field_int(checks_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
    // TLM ports are created here
    item_collected_port = new("item_collected_port", this);
  endfunction : new

  // Additional class methods
  extern task run_phase(uvm_phase phase);
  extern virtual function void perform_coverage();
  extern virtual function void perform_checks();
  extern virtual function void report_phase(uvm_phase phase);
endclass : apb_collector

// UVM run() phase
task apb_collector::run_phase(uvm_phase phase);
  apb_transfer trans_collected;
  trans_collected = new("trans_collected");
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

function void apb_collector::perform_coverage();
  // signal-level coverage goes here
endfunction : perform_coverage

function void apb_collector::perform_checks();
  // signal-level checking goes here
endfunction : perform_checks

function void apb_collector::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Report: APB collector collected %0d transfers", num_transactions), UVM_LOW);
endfunction : report_phase
