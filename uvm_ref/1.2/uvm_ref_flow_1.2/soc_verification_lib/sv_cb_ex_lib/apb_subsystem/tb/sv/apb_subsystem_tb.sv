/*-------------------------------------------------------------------------
File name   : apb_subsystem_top_tb.sv
Title       : Simulation and Verification Environment
Project     :
Created     :
Description : This file implements the SVE for the AHB-UART Environment
Notes       : The apb_subsystem_tb creates the UART env, the 
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
//----------------------------------------------------------------------

//--------------------------------------------------------------
//  Simulation Verification Environment (SVE)
//--------------------------------------------------------------
class apb_subsystem_tb extends uvm_env;

  apb_subsystem_virtual_sequencer virtual_sequencer;  // multi-channel sequencer
  ahb_pkg::ahb_env ahb0;                          // AHB UVC
  apb_pkg::apb_env apb0;                          // APB UVC
  uart_pkg::uart_env uart0;                   // UART UVC connected to UART0
  uart_pkg::uart_env uart1;                   // UART UVC connected to UART1
  spi_pkg::spi_env spi0;                      // SPI UVC connected to SPI0
  gpio_pkg::gpio_env gpio0;                   // GPIO UVC connected to GPIO0
  apb_subsystem_env apb_ss_env;

  // UVM_REG
  apb_ss_reg_model_c reg_model_apb;    // Register Model
  reg_to_ahb_adapter reg2ahb;         // Adapter Object - REG to APB
  uvm_reg_predictor#(ahb_transfer) ahb_predictor; //Predictor - APB to REG

  apb_subsystem_pkg::apb_subsystem_config apb_ss_cfg;

  // enable automation for  apb_subsystem_tb
  `uvm_component_utils_begin(apb_subsystem_tb)
     `uvm_field_object(reg_model_apb, UVM_DEFAULT | UVM_REFERENCE)
     `uvm_field_object(reg2ahb, UVM_DEFAULT | UVM_REFERENCE)
     `uvm_field_object(apb_ss_cfg, UVM_DEFAULT)
  `uvm_component_utils_end
    
  function new(input string name = "apb_subsystem_tb", input uvm_component parent=null);
    super.new(name,parent);
  endfunction

  function automatic void build_env();
     // Configure UVCs
    if (!uvm_config_db#(apb_subsystem_config)::get(this, "", "apb_ss_cfg", apb_ss_cfg)) begin
      `uvm_info(get_type_name(), "No apb_subsystem_config, creating...", UVM_LOW)
      apb_ss_cfg = apb_subsystem_config::type_id::create("apb_ss_cfg", this);
      apb_ss_cfg.uart_cfg0.apb_cfg.add_master("master", UVM_PASSIVE);
      apb_ss_cfg.uart_cfg0.apb_cfg.add_slave("spi0",  `AM_SPI0_BASE_ADDRESS,  `AM_SPI0_END_ADDRESS,  0, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg0.apb_cfg.add_slave("uart0", `AM_UART0_BASE_ADDRESS, `AM_UART0_END_ADDRESS, 0, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg0.apb_cfg.add_slave("gpio0", `AM_GPIO0_BASE_ADDRESS, `AM_GPIO0_END_ADDRESS, 0, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg0.apb_cfg.add_slave("uart1", `AM_UART1_BASE_ADDRESS, `AM_UART1_END_ADDRESS, 1, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg1.apb_cfg.add_master("master", UVM_PASSIVE);
      apb_ss_cfg.uart_cfg1.apb_cfg.add_slave("spi0",  `AM_SPI0_BASE_ADDRESS,  `AM_SPI0_END_ADDRESS,  0, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg1.apb_cfg.add_slave("uart0", `AM_UART0_BASE_ADDRESS, `AM_UART0_END_ADDRESS, 0, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg1.apb_cfg.add_slave("gpio0", `AM_GPIO0_BASE_ADDRESS, `AM_GPIO0_END_ADDRESS, 0, UVM_PASSIVE);
      apb_ss_cfg.uart_cfg1.apb_cfg.add_slave("uart1", `AM_UART1_BASE_ADDRESS, `AM_UART1_END_ADDRESS, 1, UVM_PASSIVE);
      `uvm_info(get_type_name(), {"Printing apb subsystem config:\n", apb_ss_cfg.sprint()}, UVM_MEDIUM)
    end 

     uvm_config_db#(apb_config)::set(this, "apb0", "cfg", apb_ss_cfg.uart_cfg0.apb_cfg);
     uvm_config_db#(uart_config)::set(this, "uart0", "cfg", apb_ss_cfg.uart_cfg0.uart_cfg);
     uvm_config_db#(uart_config)::set(this, "uart1", "cfg", apb_ss_cfg.uart_cfg1.uart_cfg);
     uvm_config_db#(uart_ctrl_config)::set(this, "apb_ss_env.apb_uart0", "cfg", apb_ss_cfg.uart_cfg0);
     uvm_config_db#(uart_ctrl_config)::set(this, "apb_ss_env.apb_uart1", "cfg", apb_ss_cfg.uart_cfg1);
     uvm_config_db#(apb_slave_config)::set(this, "apb_ss_env.apb_uart0", "apb_slave_cfg", apb_ss_cfg.uart_cfg0.apb_cfg.slave_configs[1]);
     uvm_config_db#(apb_slave_config)::set(this, "apb_ss_env.apb_uart1", "apb_slave_cfg", apb_ss_cfg.uart_cfg1.apb_cfg.slave_configs[3]);
     set_config_object("spi0", "spi_ve_config", apb_ss_cfg.spi_cfg, 0);
     set_config_object("gpio0", "gpio_ve_config", apb_ss_cfg.gpio_cfg, 0);

     set_config_int("*spi0.agents[0]","is_active", UVM_ACTIVE);  
     set_config_int("*gpio0.agents[0]","is_active", UVM_ACTIVE);  
     set_config_int("*ahb0.master_agent","is_active", UVM_ACTIVE);  
     set_config_int("*ahb0.slave_agent","is_active", UVM_PASSIVE);
     set_config_int("*uart0.Tx","is_active", UVM_ACTIVE);  
     set_config_int("*uart0.Rx","is_active", UVM_PASSIVE);
     set_config_int("*uart1.Tx","is_active", UVM_ACTIVE);  
     set_config_int("*uart1.Rx","is_active", UVM_PASSIVE);

     // Allocate objects
     virtual_sequencer = apb_subsystem_virtual_sequencer::type_id::create("virtual_sequencer",this);
     ahb0              = ahb_pkg::ahb_env::type_id::create("ahb0",this);
     apb0              = apb_pkg::apb_env::type_id::create("apb0",this);
     uart0             = uart_pkg::uart_env::type_id::create("uart0",this);
     uart1             = uart_pkg::uart_env::type_id::create("uart1",this);
     spi0              = spi_pkg::spi_env::type_id::create("spi0",this);
     gpio0             = gpio_pkg::gpio_env::type_id::create("gpio0",this);
     apb_ss_env        = apb_subsystem_env::type_id::create("apb_ss_env",this);

  //UVM_REG
  ahb_predictor = uvm_reg_predictor#(ahb_transfer)::type_id::create("ahb_predictor", this);
  if (reg_model_apb == null) begin
    uvm_reg::include_coverage("*", UVM_CVR_ALL);
    reg_model_apb = apb_ss_reg_model_c::type_id::create("reg_model_apb");
    reg_model_apb.build();  //NOTE: not same as build_phase: reg_model is an object
    reg_model_apb.lock_model();
  end
    // set the register model for the rest of the testbench
    uvm_config_object::set(this, "*", "reg_model_apb", reg_model_apb);
    uvm_config_object::set(this, "*uart0*", "reg_model", reg_model_apb.uart0_rm);
    uvm_config_object::set(this, "*uart1*", "reg_model", reg_model_apb.uart1_rm);


  endfunction : build_env

  function void connect_phase(uvm_phase phase);
    ahb_monitor user_ahb_monitor;
    super.connect_phase(phase);
    //UVM_REG
    reg2ahb = reg_to_ahb_adapter::type_id::create("reg2ahb");
    reg_model_apb.default_map.set_sequencer(ahb0.master_agent.sequencer, reg2ahb);  //
    reg_model_apb.default_map.set_auto_predict(1);

      if (!$cast(user_ahb_monitor, ahb0.master_agent.monitor))
        `uvm_fatal("CASTFL", "Failed to cast master monitor to user_ahb_monitor");

      // ***********************************************************
      //  Hookup virtual sequencer to interface sequencers
      // ***********************************************************
        virtual_sequencer.ahb_seqr =  ahb0.master_agent.sequencer;
      if (uart0.Tx.is_active == UVM_ACTIVE)  
        virtual_sequencer.uart0_seqr =  uart0.Tx.sequencer;
      if (uart1.Tx.is_active == UVM_ACTIVE)  
        virtual_sequencer.uart1_seqr =  uart1.Tx.sequencer;
      if (spi0.agents[0].is_active == UVM_ACTIVE)  
        virtual_sequencer.spi0_seqr =  spi0.agents[0].sequencer;
      if (gpio0.agents[0].is_active == UVM_ACTIVE)  
        virtual_sequencer.gpio0_seqr =  gpio0.agents[0].sequencer;

      virtual_sequencer.reg_model_ptr = reg_model_apb;

      apb_ss_env.monitor.set_slave_config(apb_ss_cfg.uart_cfg0.apb_cfg.slave_configs[0]);
      apb_ss_env.apb_uart0.set_slave_config(apb_ss_cfg.uart_cfg0.apb_cfg.slave_configs[1], 1);
      apb_ss_env.apb_uart1.set_slave_config(apb_ss_cfg.uart_cfg1.apb_cfg.slave_configs[3], 3);

      // ***********************************************************
      // Connect TLM ports
      // ***********************************************************
      uart0.Rx.monitor.frame_collected_port.connect(apb_ss_env.apb_uart0.monitor.uart_rx_in);
      uart0.Tx.monitor.frame_collected_port.connect(apb_ss_env.apb_uart0.monitor.uart_tx_in);
      apb0.bus_monitor.item_collected_port.connect(apb_ss_env.apb_uart0.monitor.apb_in);
      apb0.bus_monitor.item_collected_port.connect(apb_ss_env.apb_uart0.apb_in);
      user_ahb_monitor.ahb_transfer_out.connect(apb_ss_env.monitor.rx_scbd.ahb_add);
      user_ahb_monitor.ahb_transfer_out.connect(apb_ss_env.ahb_in);
      spi0.agents[0].monitor.item_collected_port.connect(apb_ss_env.monitor.rx_scbd.spi_match);


      uart1.Rx.monitor.frame_collected_port.connect(apb_ss_env.apb_uart1.monitor.uart_rx_in);
      uart1.Tx.monitor.frame_collected_port.connect(apb_ss_env.apb_uart1.monitor.uart_tx_in);
      apb0.bus_monitor.item_collected_port.connect(apb_ss_env.apb_uart1.monitor.apb_in);
      apb0.bus_monitor.item_collected_port.connect(apb_ss_env.apb_uart1.apb_in);

      // ***********************************************************
      // Connect the dut_csr ports
      // ***********************************************************
      apb_ss_env.spi_csr_out.connect(apb_ss_env.monitor.dut_csr_port_in);
      apb_ss_env.spi_csr_out.connect(spi0.dut_csr_port_in);
      apb_ss_env.gpio_csr_out.connect(gpio0.dut_csr_port_in);
  endfunction : connect_phase

  function void start_of_simulation_phase(uvm_phase phase);
    uvm_test_done.set_drain_time(this, 1000);
    uvm_test_done.set_report_verbosity_level(UVM_HIGH);
  endfunction : start_of_simulation_phase

  function automatic void build_phase(uvm_phase phase);
     super.build_phase(phase);
     build_env();
  endfunction
   
  task run_phase(uvm_phase phase);
    `uvm_info("ENV_TOPOLOGY",("APB SubSystem Virtual Sequence Testbench Topology:"), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                         _____                             "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                        | AHB |                            "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                        | UVC |                            "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                         -----                             "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                           ^                               "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                           |                               "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                           v                               "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                   ____________    _________               "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                  | AHB - APB  |  | APB UVC |              "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                  |   Bridge   |  | Passive |              "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                   ------------    ---------               "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                           ^         ^                     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                           |         |                     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("                           v         v                     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("<--------------------------------------------------------> "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("    ^        ^         ^         ^         ^         ^     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("    |        |         |         |         |         |     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("    v        v         v         v         v         v     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("  _____    _____    ______    _______    _____    _______  "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",(" | SPI |  | SMC |  | GPIO |  | UART0 |  | PCM |  | UART1 | "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("  -----    -----    ------    -------    -----    -------  "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("    ^                  ^         ^                   ^     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("    |                  |         |                   |     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("    v                  v         v                   v     "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("  _____              ______    _______            _______  "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",(" | SPI |            | GPIO |  | UART0 |          | UART1 | "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",(" | UVC |            | UVC  |  |  UVC  |          |  UVC  | "), UVM_LOW)
    `uvm_info("ENV_TOPOLOGY",("  -----              -------   -------            -------  "), UVM_LOW)
    `uvm_info(get_type_name(), {"REGISTER MODEL:\n", reg_model_apb.sprint()}, UVM_LOW)
  endtask

endclass
