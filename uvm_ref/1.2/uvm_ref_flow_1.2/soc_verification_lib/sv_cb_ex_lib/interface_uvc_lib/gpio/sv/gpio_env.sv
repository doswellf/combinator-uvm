/*-------------------------------------------------------------------------
File name   : gpio_env.sv
Title       : GPIO SystemVerilog UVM UVC
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


`ifndef GPIO_ENV_SV
`define GPIO_ENV_SV

class gpio_env extends uvm_env;

  uvm_analysis_imp#(gpio_csr, gpio_env) dut_csr_port_in;

  uvm_object cobj;
  gpio_config gpio_ve_config;

  // Virtual Interface variable
  virtual interface gpio_if gpio_if;

  // Control properties
  protected int unsigned num_agents = 1;

  // The following two bits are used to control whether checks and coverage are
  // done both in the bus monitor class and the interface.
  bit intf_checks_enable = 1; 
  bit intf_coverage_enable = 1;

  // Components of the environment
  gpio_agent agents[];

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(gpio_env)
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

    if(get_config_object("gpio_ve_config", cobj))
      if (!$cast(gpio_ve_config, cobj))
        `uvm_fatal ("CASTFL", "Failed to cast cobj to gpio_ve_config")
    else
      gpio_ve_config = gpio_config::type_id::create("gpio_ve_config", this);

    for(int i = 0; i < num_agents; i++) begin
      $sformat(inst_name, "agents[%0d]", i);
      set_config_int(inst_name, "is_active", gpio_ve_config.active_passive);
      agents[i] = gpio_agent::type_id::create(inst_name, this);
      agents[i].agent_id = i;
    end
  endfunction : build_phase

//UVM connect_phase
function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual gpio_if)::get(this, "", "gpio_if", gpio_if))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".gpio_if"})
endfunction : connect_phase

  // update_vif_enables
  protected task update_vif_enables();
    forever begin
      @(intf_checks_enable || intf_coverage_enable);
      gpio_if.has_checks <= intf_checks_enable;
      gpio_if.has_coverage <= intf_coverage_enable;
    end
  endtask : update_vif_enables

   virtual function void write(input gpio_csr cfg );
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

endclass : gpio_env

`endif // GPIO_ENV_SV

