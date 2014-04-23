class apb_env extends uvm_env;
  // Environment Configuration Parameters
  apb_config cfg;     // APB configuration object

  // Components of the environment
  apb_master_agent master;         // APB Master (Bridge)
  apb_slave_agent  slaves[];       // APB can have multiple slave agents
  apb_monitor      bus_monitor;    // Shared bus monitor
  apb_collector    bus_collector;  // Shared bus collector

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_env)
    `uvm_field_object(cfg, UVM_DEFAULT)
  `uvm_component_utils_end

  // Constructor - Required UVM syntax
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
endclass : apb_env

`ifndef ENV_NO_BUILD
// UVM build_phase
function void apb_env::build_phase(uvm_phase phase);
  uvm_object config_obj;
  super.build_phase(phase);

  // Get or create the APB UVC configuration class
  if(cfg == null)
    if (!uvm_config_db#(apb_config)::get(this, "", "cfg", cfg))  begin
    `uvm_info("NOCONFIG", "using default_apb_config", UVM_MEDIUM)
    $cast(cfg, factory.create_object_by_name("default_apb_config","cfg"));
  end
  // set the master config and slave configs before creating them
  uvm_config_object::set(this, "*", "cfg", cfg);
  foreach(cfg.slave_configs[i])
    uvm_config_object::set(this, $sformatf("slave[%0d]*", i), "cfg", cfg.slave_configs[i]);

  if (cfg.has_bus_monitor) begin
    bus_monitor = apb_monitor::type_id::create("bus_monitor",this);
    bus_collector = apb_collector::type_id::create("bus_collector",this);
  end

  master = apb_master_agent::type_id::create("master", this);
  slaves = new[cfg.slave_configs.size()];
  //for(int i = 0; i < cfg.slave_configs.size(); i++) begin
  foreach(slaves[i])
    slaves[i] = apb_slave_agent::type_id::create($sformatf("slave[%0d]", i), this);
endfunction : build_phase
`endif // ENV_NO_BUILD

function void apb_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  bus_collector.item_collected_port.connect(bus_monitor.coll_mon_port);
  bus_monitor.addr_trans_port.connect(bus_collector.addr_trans_export);
  foreach(slaves[i]) begin
    if (slaves[i].is_active == UVM_ACTIVE)
     slaves[i].sequencer.addr_trans_port.connect(bus_monitor.addr_trans_export);
  end
endfunction : connect_phase
