/*-------------------------------------------------------------------------
File name   : spi_monitor.sv
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


`ifndef SPI_MONITOR_SV
`define SPI_MONITOR_SV

class spi_monitor extends uvm_monitor;

  // This property is the virtual interfaced needed for this component to
  // view HDL signals. 
  virtual interface spi_if spi_if;

  spi_csr_s csr_s;

  // Agent Id
  protected int agent_id;

  // The following bit is used to control whether coverage is
  // done both in the monitor class and the interface.
  bit coverage_enable = 1;

  uvm_analysis_port #(spi_transfer) item_collected_port;

  // The following property holds the transaction information currently
  // begin captured (by the collect_receive_data and collect_transmit_data methods).
  protected spi_transfer trans_collected;

  // Events needed to trigger covergroups
  protected event cov_transaction;

  event new_transfer_started;
  event new_bit_started;

  // Transfer collected covergroup
  covergroup cov_trans_cg @cov_transaction;
    option.per_instance = 1;
    trans_mode : coverpoint csr_s.mode_select;
    trans_cpha : coverpoint csr_s.tx_clk_phase;
    trans_size : coverpoint csr_s.transfer_data_size {
      bins sizes[] = {0, 1, 2, 3, 8};
      illegal_bins invalid_sizes = default; }
    trans_txdata : coverpoint trans_collected.transfer_data {
      option.auto_bin_max = 8; }
    trans_rxdata : coverpoint trans_collected.receive_data {
      option.auto_bin_max = 8; }
    trans_modeXsize : cross trans_mode, trans_size;
  endgroup : cov_trans_cg

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(spi_monitor)
    `uvm_field_int(agent_id, UVM_ALL_ON)
    `uvm_field_int(coverage_enable, UVM_ALL_ON)
  `uvm_component_utils_end

  // new - constructor
  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    cov_trans_cg = new();
    cov_trans_cg.set_inst_name("spi_cov_trans_cg");
    item_collected_port = new("item_collected_port", this);
  endfunction : new

//UVM connect_phase
function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual spi_if)::get(this, "", "spi_if", spi_if))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".spi_if"})
endfunction : connect_phase

  // run phase
  virtual task run_phase(uvm_phase phase);
    fork
      collect_transactions();
    join
  endtask : run_phase

  // collect_transactions
  virtual protected task collect_transactions();
    forever begin
      @(negedge spi_if.sig_n_ss_in);
      trans_collected = new();
      -> new_transfer_started;
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
    void'(this.begin_tr(trans_collected,"SPI MONITOR"));
    if (csr_s.tx_clk_phase == 0) begin
      `uvm_info("SPI_MON", $sformatf("tx_clk_phase is %d", csr_s.tx_clk_phase), UVM_HIGH)
      for (int i = 0; i < csr_s.data_size; i++) begin
        @(negedge spi_if.sig_sclk_in);
        -> new_bit_started;
        if (csr_s.mode_select == 1) begin     //DUT MASTER mode, OVC Slave mode
          trans_collected.receive_data[i] = spi_if.sig_si;
          `uvm_info("SPI_MON", $sformatf("received data in mode_select 1 is %h", trans_collected.receive_data), UVM_HIGH)
        end else begin
          trans_collected.receive_data[i] = spi_if.sig_mi;
          `uvm_info("SPI_MON", $sformatf("received data in mode_select 0 is %h", trans_collected.receive_data), UVM_HIGH)
        end
      end
    end else begin
      `uvm_info("SPI_MON", $sformatf("tx_clk_phase is %d", csr_s.tx_clk_phase), UVM_HIGH)
      for (int i = 0; i < csr_s.data_size; i++) begin
        @(posedge spi_if.sig_sclk_in);
        -> new_bit_started;
        if (csr_s.mode_select == 1) begin     //DUT MASTER mode, OVC Slave mode
          trans_collected.receive_data[i] = spi_if.sig_si;
          `uvm_info("SPI_MON", $sformatf("received data in mode_select 1 is %h", trans_collected.receive_data), UVM_HIGH)
        end else begin
          trans_collected.receive_data[i] = spi_if.sig_mi;
          `uvm_info("SPI_MON", $sformatf("received data in mode_select 0 is %h", trans_collected.receive_data), UVM_HIGH)
        end
      end
    end
    `uvm_info("SPI_MON", $sformatf("Transfer collected :\n%s", trans_collected.sprint()), UVM_MEDIUM)
    this.end_tr(trans_collected);
  endtask : collect_transfer

endclass : spi_monitor

`endif // SPI_MONITOR_SV

