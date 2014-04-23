//------------------------------------------------------------------------------
// CLASS: apb_slave_sequencer declaration
//------------------------------------------------------------------------------
class apb_slave_sequencer extends uvm_sequencer #(apb_transfer);

  uvm_blocking_peek_port#(apb_transfer) addr_trans_port;

  apb_slave_config cfg;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_slave_sequencer)
    `uvm_field_object(cfg, UVM_DEFAULT|UVM_REFERENCE)
  `uvm_component_utils_end

  // Constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
    addr_trans_port = new("addr_trans_port", this);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(cfg == null)
      if (!uvm_config_db#(apb_slave_config)::get(this, "", "cfg", cfg))
      `uvm_error("NOCONFIG", "No configuration set")
  endfunction : build_phase

endclass : apb_slave_sequencer
