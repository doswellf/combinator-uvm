/*-------------------------------------------------------------------------
File name   : gpio_monitor.sv
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


`ifndef GPIO_MONITOR_SV
`define GPIO_MONITOR_SV

class gpio_monitor extends uvm_monitor;

  // This property is the virtual interfaced needed for this component to
  // view HDL signals. 
  virtual gpio_if gpio_if;

  gpio_csr_s csr_s;

  // Agent Id
  protected int agent_id;

  // The following two bits are used to control whether checks and coverage are
  // done both in the monitor class and the interface.
  bit checks_enable = 1;
  bit coverage_enable = 1;

  uvm_analysis_port #(gpio_transfer) item_collected_port;

  // The following property holds the transaction information currently
  // begin captured (by the collect_receive_data and collect_transmit_data methods).
  protected gpio_transfer trans_collected;
  protected gpio_transfer last_trans_collected;

  // Events needed to trigger covergroups
  protected event cov_transaction;

  event new_transfer_started;
  event new_bit_started;

  // Transfer collected covergroup
  covergroup cov_trans_cg @cov_transaction;
    option.per_instance = 1;
    bypass_mode : coverpoint csr_s.bypass_mode;
    direction_mode : coverpoint csr_s.direction_mode;
    output_enable : coverpoint csr_s.output_enable;
    trans_data : coverpoint trans_collected.monitor_data {
      option.auto_bin_max = 8; }
  endgroup : cov_trans_cg

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(gpio_monitor)
    `uvm_field_int(agent_id, UVM_ALL_ON)
    `uvm_field_int(checks_enable, UVM_ALL_ON)
    `uvm_field_int(coverage_enable, UVM_ALL_ON)
  `uvm_component_utils_end

  // new - constructor
  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    cov_trans_cg = new();
    cov_trans_cg.set_inst_name("gpio_cov_trans_cg");
    item_collected_port = new("item_collected_port", this);
  endfunction : new

//UVM connect_phase
function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual gpio_if)::get(this, "", "gpio_if", gpio_if))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".gpio_if"})
endfunction : connect_phase

  // run phase
  virtual task run_phase(uvm_phase phase);
    fork
      collect_transactions();
    join
  endtask : run_phase

  // collect_transactions
  virtual protected task collect_transactions();
      last_trans_collected = new();
    forever begin
      @(posedge gpio_if.pclk);
      trans_collected = new();
      if (m_parent != null)
        trans_collected.agent = m_parent.get_name();
      collect_transfer();
      if (coverage_enable)
         -> cov_transaction;
      item_collected_port.write(trans_collected);
    end
  endtask : collect_transactions

  // collect_transfer
  virtual protected task collect_transfer();
    void'(this.begin_tr(trans_collected,"GPIO MONITOR"));
    trans_collected.transfer_data = gpio_if.gpio_pin_out;
    trans_collected.monitor_data  = gpio_if.gpio_pin_in;
    trans_collected.output_enable = gpio_if.n_gpio_pin_oe;
    if (!last_trans_collected.compare(trans_collected))
      `uvm_info("GPIO_MON", $sformatf("Transfer collected :\n%s", trans_collected.sprint()), UVM_MEDIUM)
    last_trans_collected = trans_collected;
    this.end_tr(trans_collected);
  endtask : collect_transfer

endclass : gpio_monitor

`endif // GPIO_MONITOR_SV

