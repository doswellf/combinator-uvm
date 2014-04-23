/*-------------------------------------------------------------------------
File name   : apb_subsystem_env.sv
Title       : 
Project     :
Created     :
Description : Module env, contains the instance of scoreboard and coverage model
Notes       : 
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


//`include "apb_subsystem_defines.svh"
class apb_subsystem_env extends uvm_env; 
  
  // Component configuration classes
  apb_subsystem_config cfg;
  // These are pointers to config classes above
  spi_pkg::spi_csr spi_csr;
  gpio_pkg::gpio_csr gpio_csr;

  uart_ctrl_pkg::uart_ctrl_env apb_uart0; //block level module UVC reused - contains monitors, scoreboard, coverage.
  uart_ctrl_pkg::uart_ctrl_env apb_uart1; //block level module UVC reused - contains monitors, scoreboard, coverage.
  
  // Module monitor (includes scoreboards, coverage, checking)
  apb_subsystem_monitor monitor;

  // Pointer to the Register Database address map
  uvm_reg_block reg_model_ptr;
   
  // TLM Connections 
  uvm_analysis_port #(spi_pkg::spi_csr) spi_csr_out;
  uvm_analysis_port #(gpio_pkg::gpio_csr) gpio_csr_out;
  uvm_analysis_imp #(ahb_transfer, apb_subsystem_env) ahb_in;

  `uvm_component_utils_begin(apb_subsystem_env)
    `uvm_field_object(reg_model_ptr, UVM_DEFAULT | UVM_REFERENCE)
    `uvm_field_object(cfg, UVM_DEFAULT)
  `uvm_component_utils_end

  // constructor
  function new(input string name, input uvm_component parent=null);
    super.new(name,parent);
    // Create TLM ports
    spi_csr_out = new("spi_csr_out", this);
    gpio_csr_out = new("gpio_csr_out", this);
    ahb_in = new("apb_in", this);
    spi_csr  = spi_pkg::spi_csr::type_id::create("spi_csr", this) ;
    gpio_csr = gpio_pkg::gpio_csr::type_id::create("gpio_csr", this) ;
  endfunction

  // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void write(ahb_transfer transfer);
  extern virtual function void write_effects(ahb_transfer transfer);
  extern virtual function void read_effects(ahb_transfer transfer);

endclass : apb_subsystem_env

function void apb_subsystem_env::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Configure the device
  if (!uvm_config_db#(apb_subsystem_config)::get(this, "", "cfg", cfg)) begin
    `uvm_info(get_type_name(),"No apb_subsystem_config creating...", UVM_LOW)
    set_inst_override_by_type("cfg", apb_subsystem_config::get_type(),
                                     default_apb_subsystem_config::get_type());
    cfg = apb_subsystem_config::type_id::create("cfg");
  end
  // build system level monitor
  monitor = apb_subsystem_monitor::type_id::create("monitor",this);
    apb_uart0  = uart_ctrl_pkg::uart_ctrl_env::type_id::create("apb_uart0",this);
    apb_uart1  = uart_ctrl_pkg::uart_ctrl_env::type_id::create("apb_uart1",this);
endfunction : build_phase
  
function void apb_subsystem_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

// UVM_REG: write method for APB transfers - handles Register Operations
function void apb_subsystem_env::write(ahb_transfer transfer);
    if (transfer.direction == WRITE) begin
      `uvm_info(get_type_name(),
          $sformatf("Write -- calling update() with address = 'h%0h, data = 'h%0h",
          transfer.address, transfer.data), UVM_MEDIUM)
      write_effects(transfer);
    end
    else if (transfer.direction == READ) begin
      if ((transfer.address >= `AM_SPI0_BASE_ADDRESS) && (transfer.address <= `AM_SPI0_END_ADDRESS)) begin
        `uvm_info(get_type_name(), $sformatf("Read -- calling compare_and_update() with address = 'h%0h, data = 'h%0h", transfer.address, transfer.data), UVM_MEDIUM)
      end
    end else
        `uvm_error("REGMEM1", "Unsupported access!!!")
endfunction : write

// UVM_REG: Update CONFIG based on APB writes to config registers
function void apb_subsystem_env::write_effects(ahb_transfer transfer);
    case (transfer.address)
      `AM_SPI0_BASE_ADDRESS + `SPI_CTRL_REG : begin
                                                  spi_csr.mode_select        = 1'b1;
                                                  spi_csr.tx_clk_phase       = transfer.data[10];
                                                  spi_csr.rx_clk_phase       = transfer.data[9];
                                                  spi_csr.transfer_data_size = transfer.data[6:0];
                                                  spi_csr.get_data_size_as_int();
                                                  spi_csr.Copycfg_struct();
                                                  spi_csr_out.write(spi_csr);
      `uvm_info("USR_MONITOR", $sformatf("SPI CSR is \n%s", spi_csr.sprint()), UVM_MEDIUM)
                                                end
      `AM_SPI0_BASE_ADDRESS + `SPI_DIV_REG  : begin
                                                  spi_csr.baud_rate_divisor  = transfer.data[15:0];
                                                  spi_csr.Copycfg_struct();
                                                  spi_csr_out.write(spi_csr);
                                                end
      `AM_SPI0_BASE_ADDRESS + `SPI_SS_REG   : begin
                                                  spi_csr.n_ss_out           = transfer.data[7:0];
                                                  spi_csr.Copycfg_struct();
                                                  spi_csr_out.write(spi_csr);
                                                end
      `AM_GPIO0_BASE_ADDRESS + `GPIO_BYPASS_MODE_REG : begin
                                                  gpio_csr.bypass_mode       = transfer.data[0];
                                                  gpio_csr.Copycfg_struct();
                                                  gpio_csr_out.write(gpio_csr);
                                                end
      `AM_GPIO0_BASE_ADDRESS + `GPIO_DIRECTION_MODE_REG : begin
                                                  gpio_csr.direction_mode    = transfer.data[0];
                                                  gpio_csr.Copycfg_struct();
                                                  gpio_csr_out.write(gpio_csr);
                                                end
      `AM_GPIO0_BASE_ADDRESS + `GPIO_OUTPUT_ENABLE_REG : begin
                                                  gpio_csr.output_enable     = transfer.data[0];
                                                  gpio_csr.Copycfg_struct();
                                                  gpio_csr_out.write(gpio_csr);
                                                end
      default: `uvm_info("USR_MONITOR", $sformatf("Write access not to Control/Sataus Registers"), UVM_HIGH)
    endcase
endfunction : write_effects

function void apb_subsystem_env::read_effects(ahb_transfer transfer);
  // Nothing for now
endfunction : read_effects


