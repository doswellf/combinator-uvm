/**************************************************************************
  Example 5-12: APB Master Agent

  To run:   %  irun -uvm ex5-12_apb_master_agent.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-12_apb_master_agent.sv
**************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_if.sv"
`include "sv/apb_config.sv"
`include "sv/apb_transfer.sv"
`include "sv/apb_collector.sv"
`include "sv/apb_monitor.sv"
`include "sv/apb_master_driver.sv"
`include "sv/apb_master_sequencer.sv"

//------------------------------------------------------------------------------
// CLASS: apb_master_agent
//------------------------------------------------------------------------------
class apb_master_agent extends uvm_agent;

  // This built-in field determines whether an agent is active or passive.
  // uvm_active_passive_enum is_active = UVM_ACTIVE;

  // Agent components
  apb_monitor   monitor;
  apb_collector collector;
  apb_master_sequencer sequencer;
  apb_master_driver    driver;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_master_agent)
     `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  
  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  
endclass : apb_master_agent

// UVM build_phase()
function void apb_master_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Always create the collector and monitor
  monitor = apb_monitor::type_id::create("monitor", this);
  collector = apb_collector::type_id::create("collector", this);
  if(is_active == UVM_ACTIVE) begin
    sequencer = apb_master_sequencer::type_id::create("sequencer",this);
    driver = apb_master_driver::type_id::create("driver",this);
  end
endfunction : build_phase

//Use UVM connect_phase() to connect the component TLM ports
function void apb_master_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  collector.item_collected_port.connect(monitor.coll_mon_port);
  if (is_active == UVM_ACTIVE) begin
    // Connect the driver to the sequencer using TLM interface
    driver.seq_item_port.connect(sequencer.seq_item_export);
  end
endfunction : connect_phase
