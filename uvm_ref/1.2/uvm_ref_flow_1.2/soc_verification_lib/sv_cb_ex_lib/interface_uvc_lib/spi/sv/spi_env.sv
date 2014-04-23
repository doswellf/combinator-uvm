/*-------------------------------------------------------------------------
File name   : spi_env.sv
Title       : SPI SystemVerilog UVM UVC
Project     : SystemVerilog UVM Cluster Level Verification
Created     :
Description : 
Notes       :  
---------------------------------------------------------------------------*/
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


`ifndef SPI_ENV_SV
`define SPI_ENV_SV

class spi_env extends uvm_env;

  uvm_analysis_imp#(spi_csr, spi_env) dut_csr_port_in;

  uvm_object cobj;
  spi_config spi_ve_config;

  // Virtual Interface variable
  virtual interface spi_if spi_if;

  // Control properties
  protected int unsigned num_agents = 1;

  // The following two bits are used to control whether checks and coverage are
  // done both in the bus monitor class and the interface.
  bit intf_checks_enable = 1; 
  bit intf_coverage_enable = 1;

  // Components of the environment
  spi_agent agents[];

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(spi_env)
    `uvm_field_int(num_agents, UVM_ALL_ON)
    `uvm_field_int(intf_checks_enable, UVM_ALL_ON)
    `uvm_field_int(intf_coverage_enable, UVM_ALL_ON)
  `uvm_component_utils_end

  // new - constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
    dut_csr_port_in = new ("dut_csr_port_in", this);
  endfunction : new

  // build
  function void build_phase(uvm_phase phase);
    string inst_name;
    super.build_phase(phase);
    agents = new[num_agents];

    if(get_config_object("spi_ve_config", cobj))
      if (!$cast(spi_ve_config, cobj))
        `uvm_fatal ("CASTFL", "Failed to cast cobj to spi_ve_config")
    else
      spi_ve_config = spi_config::type_id::create("spi_ve_config", this);

    for(int i = 0; i < num_agents; i++) begin
      $sformat(inst_name, "agents[%0d]", i);
      set_config_int(inst_name, "is_active", spi_ve_config.active_passive);
      agents[i] = spi_agent::type_id::create(inst_name, this);
      agents[i].agent_id = i;
    end
  endfunction : build_phase

//UVM connect_phase
function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual spi_if)::get(this, "", "spi_if", spi_if))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".spi_if"})
endfunction : connect_phase

  // update_vif_enables
  protected task update_vif_enables();
    forever begin
      @(intf_checks_enable || intf_coverage_enable);
      spi_if.has_checks <= intf_checks_enable;
      spi_if.has_coverage <= intf_coverage_enable;
    end
  endtask : update_vif_enables

   virtual function void write(input spi_csr cfg );
    for(int i = 0; i < num_agents; i++) begin
      agents[i].assign_csr(cfg.csr_s);
    end
   endfunction

  // implement run task
  task run_phase(uvm_phase phase);
    fork
      update_vif_enables();
    join
  endtask : run_phase

endclass : spi_env

`endif // SPI_ENV_SV

