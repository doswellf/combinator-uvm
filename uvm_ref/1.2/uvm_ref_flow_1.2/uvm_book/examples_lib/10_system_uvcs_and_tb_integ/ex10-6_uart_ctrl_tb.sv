/***************************************************************************
  Example 10-6: UART Controller Testbench

  Kit Location : $UVM_REF_HOME/soc_verification_libs/sv_cb_ex_lib/uart_ctrl/tb/sv/uart_ctrl_tb.sv

***************************************************************************/
/*-------------------------------------------------------------------------
File name   : uart_ctrl_tb.sv
Title       : Simulation and Verification Environment
Project     :
Created     :
Description : This file implements the testbench for the UART Environment
Notes       : The uart_ctrl_tb creates the UART env, the 
            : APB env and the scoreboard. It also randomizes the UART 
            : CSR settings and passes it to both the env's.
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
 
`include "uart_ctrl_reg_seq_lib.sv"

//Include UART Controller-specific UVC sequences
`include "uart_ctrl_seq_lib.sv"
`include "uart_ctrl_virtual_seq_lib.sv"

//--------------------------------------------------------------
//  Simulation Verification Environment 
//--------------------------------------------------------------
class uart_ctrl_tb extends uvm_env;

  // UVC Components
  apb_pkg::apb_env   apb0;          // APB UVC
  uart_pkg::uart_env uart0;         // UART UVC
  uart_ctrl_env      uart_ctrl0;    // Module UVC
  
  // Virtual sequencer
  uart_ctrl_virtual_sequencer virtual_sequencer;

  // Configurations object
  uart_ctrl_config cfg;

  // UVM_REG - Register Model
  uart_ctrl_reg_model_c reg_model;    // Register Model

  // Enable coverage for the register model
  bit coverage_enable = 1;

  uvm_table_printer printer = new();

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(uart_ctrl_tb)
     `uvm_field_object(reg_model, UVM_DEFAULT | UVM_REFERENCE)
     `uvm_field_object(cfg, UVM_DEFAULT)
     `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_component_utils_end

  // Constructor - required UVM syntax
  function new(input string name, input uvm_component parent=null);
    super.new(name,parent);
  endfunction

  // Additional class methods
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void update_config(uart_ctrl_config uart_ctrl_cfg);

endclass : uart_ctrl_tb

  function void uart_ctrl_tb::start_of_simulation_phase(uvm_phase phase);
    uvm_test_done.set_drain_time(this, 1000);
    uvm_test_done.set_report_verbosity_level(UVM_HIGH);
  endfunction : start_of_simulation_phase

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
    if (uart0.Tx.cfg.is_tx_active == UVM_ACTIVE)  
       virtual_sequencer.uart_seqr =  uart0.Tx.sequencer;

    //SETUP THE UART SLAVE CONFIG
    uart_ctrl0.set_slave_config(cfg.apb_cfg.slave_configs[0], 0);

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

  task uart_ctrl_tb::run_phase(uvm_phase phase);
    printer.knobs.depth = 5;
    printer.knobs.name_width = 25;
    printer.knobs.type_width = 20;
    printer.knobs.value_width = 20;
    `uvm_info(get_type_name(),
       {"UART_Controller Testbench Topology:\n", this.sprint(printer)},
       UVM_LOW)
      `uvm_info(get_type_name(), {"REGISTER MODEL:\n", reg_model.sprint()}, UVM_MEDIUM)
  endtask

  function void uart_ctrl_tb::update_config(uart_ctrl_config uart_ctrl_cfg);
     `uvm_info(get_type_name(), {"Update Config\n", uart_ctrl_cfg.sprint()}, UVM_HIGH)
     cfg = uart_ctrl_cfg;
     // SHOULD NOT BE NECESSARY - EVERYTHING IS A POINTER
     uart_ctrl0.update_config(uart_ctrl_cfg, 0);
     uart0.update_config(uart_ctrl_cfg.uart_cfg);
     apb0.update_config(uart_ctrl_cfg.apb_cfg);
  endfunction : update_config
