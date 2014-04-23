/****************************************************************
  File: apb_slave_agent.sv
  Description: APB Slave Agent Definition
****************************************************************/
`ifndef APB_SLAVE_AGENT_SV
`define APB_SLAVE_AGENT_SV

//------------------------------------------------------------------------------
// CLASS: apb_slave_agent
//------------------------------------------------------------------------------
class apb_slave_agent extends uvm_agent;

  // This field determines whether an agent is active or passive.
  uvm_active_passive_enum is_active = UVM_ACTIVE;

  // Slave Configuration Information:  name, is_active, psel_index,
  //                                   start_address, end_address
  apb_slave_config cfg;

  // Agent components
  apb_monitor   monitor;
  apb_collector collector;
  apb_slave_sequencer sequencer;
  apb_slave_driver    driver;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_slave_agent)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  
  // Additional class methods
  extern virtual function void build();
  extern virtual function void connect();
  extern virtual function void assign_vi(virtual interface apb_if vif);

endclass : apb_slave_agent

// UVM build() phase
function void apb_slave_agent::build();
  super.build();
  if (cfg != null) is_active = cfg.is_active;
  // Always create the collector and monitor
  collector = apb_collector::type_id::create("collector", this);
  monitor = apb_monitor::type_id::create("monitor", this);
  if(is_active == UVM_ACTIVE) begin
    sequencer = apb_slave_sequencer::type_id::create("sequencer",this);
    driver = apb_slave_driver::type_id::create("driver",this);
  end
endfunction : build

// UVM connect() phase
function void apb_slave_agent::connect();
  collector.item_collected_port.connect(monitor.coll_mon_port);
  monitor.addr_trans_port.connect(collector.addr_trans_export);
  if (is_active == UVM_ACTIVE) begin
    // Connect the driver to the sequencer using TLM interface
    driver.seq_item_port.connect(sequencer.seq_item_export);
  end
endfunction : connect

// assign the virtual interfaces of the agent's children
function void apb_slave_agent::assign_vi(virtual interface apb_if vif);
  collector.vif = vif;
  if (is_active == UVM_ACTIVE) begin
    if(driver != null) driver.vif = vif;
  end
endfunction : assign_vi

`endif  // APB_SLAVE_AGENT_SV
