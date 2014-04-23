/**************************************************************************
  Example 9-8: UART Controller Testbench with Register Model Components

  Description : This file implements the testbench for the UART Environment
  This example is part of the soc_ex design and does not run stand-alone
**************************************************************************/

//--------------------------------------------------------------
//  Testbench
//--------------------------------------------------------------
class uart_ctrl_tb extends uvm_env;

  // Configurations object
  uart_ctrl_config cfg;

  // UVC Components
  apb_pkg::apb_env   apb0;          // APB UVC
  uart_pkg::uart_env uart0;         // UART UVC
  uart_ctrl_env      uart_ctrl0;    // Module UVC
  
  // Virtual sequencer
  uart_ctrl_virtual_sequencer virtual_sequencer;

  // UVM_REG - Register Model
  uart_ctrl_reg_model_c reg_model;    // Register Model
  // Enable coverage for the register model
  bit coverage_enable = 1;

  uvm_table_printer printer = new();

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(uart_ctrl_tb)
     `uvm_field_object(reg_model, UVM_DEFAULT | UVM_REFERENCE)
     `uvm_field_int(coverage_enable, UVM_DEFAULT)
     `uvm_field_object(cfg, UVM_DEFAULT)
  `uvm_component_utils_end

  // Constructor - required UVM syntax
  function new(input string name, input uvm_component parent=null);
    super.new(name,parent);
  endfunction

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task reset_reg_model();

endclass : uart_ctrl_tb
 function void uart_ctrl_tb::build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Configure UVCs
    if (cfg == null)
      if (!uvm_config_db#(uart_ctrl_config)::get(this, "", "cfg", cfg)) begin
        `uvm_info("NOCONFIG", "No uart_ctrl_config, creating...", UVM_LOW)
        cfg = uart_ctrl_config::type_id::create("cfg", this);
        cfg.apb_cfg.add_master("master", UVM_ACTIVE);
        cfg.apb_cfg.add_slave("uart0", 32'h000000, 32'h81FFFF, 0, UVM_PASSIVE);
        `uvm_info(get_type_name(), {"Printing cfg:\n", cfg.sprint()}, UVM_MEDIUM)
      end
   // Configure the sub-components. 
   uvm_config_object::set(this, "apb0", "cfg", cfg.apb_cfg);
   uvm_config_object::set(this, "uart0", "cfg", cfg.uart_cfg);
   uvm_config_object::set(this, "uart_ctrl0", "cfg", cfg);
   uvm_config_object::set(this, "virtual_sequencer", "cfg", cfg);
   uvm_config_object::set(this, "uart_ctrl0", "apb_slave_cfg", cfg.apb_cfg.slave_configs[0]);

    //UVM_REG - Create and configure the register model
    if (reg_model == null) begin
      // Only enable reg model coverage if enabled for the testbench
      if (coverage_enable == 1) uvm_reg::include_coverage("*", UVM_CVR_ALL);
      reg_model = uart_ctrl_reg_model_c::type_id::create("reg_model");
      reg_model.build();  //NOTE: not same as build_phase: reg_model is an object
      reg_model.lock_model();
    end
    // set the register model for the rest of the testbench
    uvm_config_object::set(this, "*", "reg_model", reg_model);

    // Create APB, UART, Module UVC and Virtual Sequencer
    apb0              = apb_pkg::apb_env::type_id::create("apb0",this);
    uart0             = uart_pkg::uart_env::type_id::create("uart0",this);
    uart_ctrl0        = uart_ctrl_env::type_id::create("uart_ctrl0",this);
    virtual_sequencer = uart_ctrl_virtual_sequencer::type_id::create("virtual_sequencer",this);
  endfunction : build_phase

  // UVM connect_phase
  function void uart_ctrl_tb::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    //UVM_REG - set the sequencer and adapter for the register model
    reg_model.default_map.set_sequencer(apb0.master.sequencer, uart_ctrl0.reg2apb);  //
    // ***********************************************************
    //  Hookup virtual sequencer to interface sequencers
    // ***********************************************************
    virtual_sequencer.apb_seqr = apb0.master.sequencer;
    virtual_sequencer.uart_seqr =  uart0.Tx.sequencer;

    //SETUP THE UART SLAVE CONFIG
    uart_ctrl0.set_slave_config(cfg.apb_cfg.slave_configs[0], 0);

    // ***********************************************************
    // ***********************************************************
    // Connect TLM ports
    // ***********************************************************
    uart0.Rx.monitor.frame_collected_port.connect(uart_ctrl0.monitor.uart_rx_in);
    uart0.Tx.monitor.frame_collected_port.connect(uart_ctrl0.monitor.uart_tx_in);
    apb0.bus_monitor.item_collected_port.connect(uart_ctrl0.monitor.apb_in);
    apb0.bus_monitor.item_collected_port.connect(uart_ctrl0.apb_in);
    apb0.bus_monitor.item_collected_port.connect(uart_ctrl0.apb_predictor.bus_in);

    // ***********************************************************
    // Connect the dut_cfg ports
    // ***********************************************************
    uart_ctrl0.uart_cfg_out.connect(uart0.dut_cfg_port_in);

endfunction : connect_phase

task uart_ctrl_tb::reset_reg_model();
  forever begin
   wait (top.reset == 1)
   `uvm_info(get_type_name(), "Resetting Registers", UVM_LOW);
   reg_model.reset();
  end
endtask

task uart_ctrl_tb::run_phase(uvm_phase phase);
   fork
     super.run_phase(phase);
     reset_reg_model();
   join_none
endtask
