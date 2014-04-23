/*-------------------------------------------------------------------------
File name   : spi_driver.sv
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


`ifndef SPI_DRIVER_SV
`define SPI_DRIVER_SV

class spi_driver extends uvm_driver #(spi_transfer);

  // The virtual interface used to drive and view HDL signals.
  virtual spi_if spi_if;

  spi_monitor monitor;
  spi_csr_s csr_s;

  // Agent Id
  protected int agent_id;

  // Provide implmentations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(spi_driver)
    `uvm_field_int(agent_id, UVM_ALL_ON)
  `uvm_component_utils_end

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
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
      get_and_drive();
      reset_signals();
    join
  endtask : run_phase

  // get_and_drive 
  virtual protected task get_and_drive();
    uvm_sequence_item item;
    spi_transfer this_trans;
    @(posedge spi_if.sig_n_p_reset);
    forever begin
      @(posedge spi_if.sig_pclk);
      seq_item_port.get_next_item(req);
      if (!$cast(this_trans, req))
        `uvm_fatal("CASTFL", "Failed to cast req to this_trans in get_and_drive")
      drive_transfer(this_trans);
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  // reset_signals
  virtual protected task reset_signals();
      @(negedge spi_if.sig_n_p_reset);
      spi_if.sig_slave_out_clk  <= 'b0;
      spi_if.sig_n_so_en        <= 'b1;
      spi_if.sig_so             <= 'bz;
      spi_if.sig_n_ss_en        <= 'b1;
      spi_if.sig_n_ss_out       <= '1;
      spi_if.sig_n_sclk_en      <= 'b1;
      spi_if.sig_sclk_out       <= 'b0;
      spi_if.sig_n_mo_en        <= 'b1;
      spi_if.sig_mo             <= 'b0;
  endtask : reset_signals

  // drive_transfer
  virtual protected task drive_transfer (spi_transfer trans);
    if (csr_s.mode_select == 1) begin       //DUT MASTER mode, OVC SLAVE mode
      @monitor.new_transfer_started;
      for (int i = 0; i < csr_s.data_size; i++) begin
        @monitor.new_bit_started;
        spi_if.sig_n_so_en <= 1'b0;
        spi_if.sig_so <= trans.transfer_data[i];
      end
      spi_if.sig_n_so_en <= 1'b1;
      `uvm_info("SPI_DRIVER", $sformatf("Transfer sent :\n%s", trans.sprint()), UVM_MEDIUM)
    end
  endtask : drive_transfer

endclass : spi_driver

`endif // SPI_DRIVER_SV

