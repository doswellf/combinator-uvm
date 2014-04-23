/****************************************************************
  File: apb_mster_agent.sv
  Description: APB Master Agent Definition
****************************************************************/
`ifndef APB_MASTER_AGENT_SV
`define APB_MASTER_AGENT_SV

//------------------------------------------------------------------------------
// CLASS: apb_master_agent
//------------------------------------------------------------------------------
class apb_master_agent extends uvm_agent;

  // This field determines whether an agent is active or passive.
//  uvm_active_passive_enum is_active = UVM_ACTIVE;

  // Configuration information: (master_config: name, is_active)
  apb_config cfg;

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
  collector = apb_collector::type_id::create("collector", this);
  monitor = apb_monitor::type_id::create("monitor", this);
  if(is_active == UVM_ACTIVE) begin
    sequencer = apb_master_sequencer::type_id::create("sequencer",this);
    driver = apb_master_driver::type_id::create("driver",this);
  end
endfunction : build_phase

// UVM connect_phase()
function void apb_master_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  collector.item_collected_port.connect(monitor.coll_mon_port);
  monitor.addr_trans_port.connect(collector.addr_trans_export);
  if (is_active == UVM_ACTIVE) begin
    // Connect the driver to the sequencer using TLM interface
    driver.seq_item_port.connect(sequencer.seq_item_export);
  end
endfunction : connect_phase

`endif  // APB_MASTER_AGENT_SV
