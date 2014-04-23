/**********************************************************************
  Example 10-3: UART Controller Module UVC

  Kit Location : $UVM_REF_HOME/soc_verification_libs/sv_cb_ex_lib/uart_ctrl/sv/uart_ctrl_env.sv
*********************************************************************/

`include "uart_ctrl_defines.svh"
class uart_ctrl_env extends uvm_env; 
  
  // Component configuration classes
  uart_ctrl_config cfg;
  // These are pointers to config classes above
  uart_config uart_cfg;
  apb_slave_config apb_slave_cfg;

  // Module monitor (includes scoreboards, coverage, checking)
  uart_ctrl_monitor monitor;

  // Control bit
  bit div_en;

  // UVM_REG: Pointer to the Register Model
  uart_ctrl_reg_model_c reg_model;
  // Adapter sequence and predictor
  reg_to_apb_adapter reg2apb;   // Adapter Object REG to APB
  uvm_reg_predictor#(apb_transfer) apb_predictor;  // Precictor - APB to REG
  
  // TLM Connections 
  uvm_analysis_port #(uart_config) uart_cfg_out;
  uvm_analysis_imp #(apb_transfer, uart_ctrl_env) apb_in;

  `uvm_component_utils_begin(uart_ctrl_env)
    `uvm_field_object(reg_model, UVM_DEFAULT | UVM_REFERENCE)
    `uvm_field_object(reg2apb, UVM_DEFAULT | UVM_REFERENCE)
    `uvm_field_object(cfg, UVM_DEFAULT)
  `uvm_component_utils_end

  // constructor
  function new(input string name, input uvm_component parent=null);
    super.new(name,parent);
    // Create TLM ports
    uart_cfg_out = new("uart_cfg_out", this);
    apb_in = new("apb_in", this);
  endfunction

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void write(apb_transfer transfer);
  extern virtual function void update_config(uart_ctrl_config uart_ctrl_cfg, int index);
  extern virtual function void set_slave_config(apb_slave_config _slave_cfg, int index);
  extern virtual function void set_uart_config(uart_config _uart_cfg);
  extern virtual function void write_effects(apb_transfer transfer);
  extern virtual function void read_effects(apb_transfer transfer);

endclass : uart_ctrl_env

function void uart_ctrl_env::build_phase(uvm_phase phase);
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

  // build system level monitor
  monitor = uart_ctrl_monitor::type_id::create("monitor",this);

  // UVMREG: Get the register model, create the adapter and predictor
  if (reg_model == null)
    if (!uvm_config_db#(uvm_reg_block)::get(this, "", "model", reg_model))
      `uvm_error("NO_REG_CONFIG", "No register model found...")
  reg2apb = reg_to_apb_adapter::type_id::create("reg2apb");
  apb_predictor = uvm_reg_predictor#(apb_transfer)::type_id::create("apb_predictor", this);
endfunction : build_phase
  
function void uart_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  //UVMREG - Connect adapter to register sequencer and predictor
  apb_predictor.map = reg_model.default_map;
  apb_predictor.adapter = reg2apb;
endfunction : connect_phase

// UVM_REG: write method for APB transfers - handles Register Operations
function void uart_ctrl_env::write(apb_transfer transfer);
  if (apb_slave_cfg.check_address_range(transfer.addr)) begin
    if (transfer.direction == APB_WRITE) begin
      `uvm_info(get_type_name(),
          $sformatf("APB_WRITE: addr = 'h%0h, data = 'h%0h",
          transfer.addr, transfer.data), UVM_MEDIUM)
      write_effects(transfer);
    end
    else if (transfer.direction == APB_READ) begin
      `uvm_info(get_type_name(),
          $sformatf("APB_READ: addr = 'h%0h, data = 'h%0h",
          transfer.addr, transfer.data), UVM_MEDIUM)
        read_effects(transfer);
    end else
      `uvm_error("REGMEM", "Unsupported access!!!")
  end
endfunction : write

// UVM_REG: Update CONFIG based on APB writes to config registers
function void uart_ctrl_env::write_effects(apb_transfer transfer);
  case (transfer.addr)
    apb_slave_cfg.start_address + `LINE_CTRL : begin
                                            uart_cfg.char_length = transfer.data[1:0];
                                            uart_cfg.parity_mode = transfer.data[5:4];
                                            uart_cfg.parity_en   = transfer.data[3];
                                            uart_cfg.nbstop      = transfer.data[2];
                                            div_en = transfer.data[7];
                                            uart_cfg.ConvToIntChrl();
                                            uart_cfg.ConvToIntStpBt();
                                            uart_cfg_out.write(uart_cfg);
                                          end
    apb_slave_cfg.start_address + `DIVD_LATCH1 : begin
                                            if (div_en) begin
                                            uart_cfg.baud_rate_gen = transfer.data[7:0];
                                            uart_cfg_out.write(uart_cfg);
                                            end
                                          end
    apb_slave_cfg.start_address + `DIVD_LATCH2 : begin
                                            if (div_en) begin
                                            uart_cfg.baud_rate_div = transfer.data[7:0];
                                            uart_cfg_out.write(uart_cfg);
                                            end
                                          end
    default: `uvm_warning("REGMEM2", "Write access not to Control/Sataus Registers")
  endcase
  set_uart_config(uart_cfg);
endfunction : write_effects

function void uart_ctrl_env::read_effects(apb_transfer transfer);
  // Nothing for now
endfunction : read_effects

function void uart_ctrl_env::update_config(uart_ctrl_config uart_ctrl_cfg, int index);
  `uvm_info(get_type_name(), {"Updating Config\n", uart_ctrl_cfg.sprint}, UVM_HIGH)
  cfg = uart_ctrl_cfg;
  // Update these configs also (not really necessary since all are pointers)
  uart_cfg = uart_ctrl_cfg.uart_cfg;
  apb_slave_cfg = cfg.apb_cfg.slave_configs[index];
  monitor.cfg = uart_ctrl_cfg;
endfunction : update_config

function void uart_ctrl_env::set_slave_config(apb_slave_config _slave_cfg, int index);
  monitor.cfg.apb_cfg.slave_configs[index]  = _slave_cfg;
  monitor.set_slave_config(_slave_cfg, index);
endfunction : set_slave_config

function void uart_ctrl_env::set_uart_config(uart_config _uart_cfg);
  `uvm_info(get_type_name(), {"Setting Config\n", _uart_cfg.sprint()}, UVM_HIGH)
  monitor.cfg.uart_cfg  = _uart_cfg;
  monitor.set_uart_config(_uart_cfg);
endfunction : set_uart_config
