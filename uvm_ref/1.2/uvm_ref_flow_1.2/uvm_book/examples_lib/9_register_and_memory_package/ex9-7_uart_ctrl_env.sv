/**********************************************************************
Example 9-7: UART Controller Module UVC with Register Layer Additions

No testcase for this example.  Please run the full example
***********************************************************************/
class uart_ctrl_env extends uvm_env; 
  
  // Component configuration classes
  uart_ctrl_config cfg;

  // UVM_REG: Pointer to the Register Model
  uart_ctrl_reg_model_c reg_model;
  // Adapter sequence and predictor
  reg_to_apb_adapter reg2apb;   // Adapter Object REG to APB
  uvm_reg_predictor#(apb_transfer) apb_predictor;  // Precictor - APB to REG
  
  `uvm_component_utils_begin(uart_ctrl_env)
    `uvm_field_object(reg_model, UVM_DEFAULT | UVM_REFERENCE)
    `uvm_field_object(reg2apb, UVM_DEFAULT | UVM_REFERENCE)
    `uvm_field_object(cfg, UVM_DEFAULT)
  `uvm_component_utils_end

  // constructor
  function new(input string name, input uvm_component parent=null);
    super.new(name,parent);
  endfunction

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : uart_ctrl_env

function void uart_ctrl_env::build_phase(uvm_phase phase);
  uart_config uart_cfg;
  apb_slave_config apb_slave_cfg;
  super.build_phase(phase);
  // Get or create the UART CONTROLLER config class
  if (cfg == null) //begin
    if (!uvm_config_db#(uart_ctrl_config)::get(this, "", "cfg", cfg)) begin
    `uvm_info("NOCONFIG", "No uart_ctrl_config creating...", UVM_LOW)
    set_inst_override_by_type("cfg", uart_ctrl_config::get_type(),
                                     default_uart_ctrl_config::get_type());
    cfg = uart_ctrl_config::type_id::create("cfg");
    //if (!cfg.randomize()) `uvm_error("RNDFAIL", "Config Randomization Failed")
  end
  if (apb_slave_cfg == null) //begin
    if (!uvm_config_db#(apb_slave_config)::get(this, "", "apb_slave_cfg", apb_slave_cfg)) begin
    `uvm_info("NOCONFIG", "No apb_slave_config ..", UVM_LOW)
    apb_slave_cfg = cfg.apb_cfg.slave_configs[0];
  end
  //uvm_config_db#(uart_ctrl_config)::set(this, "monitor", "cfg", cfg);
  uvm_config_object::set(this, "monitor", "cfg", cfg);
  uart_cfg = cfg.uart_cfg;

  // UVMREG: Create the adapter and predictor
  reg2apb = reg_to_apb_adapter::type_id::create("reg2apb");
  apb_predictor = uvm_reg_predictor#(apb_transfer)::type_id::create("apb_predictor", this);
endfunction : build_phase
  
function void uart_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  //UVMREG - Connect adapter to register sequencer and predictor
  apb_predictor.map = reg_model.default_map;
  apb_predictor.adapter = reg2apb;
endfunction : connect_phase
