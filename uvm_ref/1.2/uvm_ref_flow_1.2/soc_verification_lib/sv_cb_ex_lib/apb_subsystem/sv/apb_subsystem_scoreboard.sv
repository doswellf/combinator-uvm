/*-------------------------------------------------------------------------
File name   : apb_subsystem_scoreboard.sv
Title       : AHB - SPI Scoreboard
Project     :
Created     :
Description : Scoreboard for data integrity check between AHB UVC and SPI UVC
Notes       : Two similar scoreboards one for read and one for write
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
`uvm_analysis_imp_decl(_ahb)
`uvm_analysis_imp_decl(_spi)

class spi2ahb_scbd extends uvm_scoreboard;
  bit [7:0] data_to_ahb[$];
  bit [7:0] temp1;

  spi_pkg::spi_csr_s csr;
  apb_pkg::apb_slave_config slave_cfg;

  `uvm_component_utils(spi2ahb_scbd)

  uvm_analysis_imp_ahb #(ahb_pkg::ahb_transfer, spi2ahb_scbd) ahb_match;
  uvm_analysis_imp_spi #(spi_pkg::spi_transfer, spi2ahb_scbd) spi_add;
   
  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    spi_add  = new("spi_add", this);
    ahb_match = new("ahb_match", this);
  endfunction : new

  // implement SPI Tx analysis port from reference model
  virtual function void write_spi(spi_pkg::spi_transfer transfer);
    data_to_ahb.push_back(transfer.transfer_data[7:0]);	
  endfunction : write_spi
     
  // implement APB READ analysis port from reference model
  virtual function void write_ahb(input ahb_pkg::ahb_transfer transfer);

    if ((transfer.address ==   (slave_cfg.start_address + `SPI_RX0_REG)) && (transfer.direction.name() == "READ"))
      begin
        temp1 = data_to_ahb.pop_front();
       
        if (temp1 == transfer.data[7:0]) 
          `uvm_info("SCRBD", $sformatf("####### PASS : AHB RECEIVED CORRECT DATA from %s  expected = %h, received = %h", slave_cfg.name, temp1, transfer.data), UVM_MEDIUM)
        else begin
          `uvm_error(get_type_name(), $sformatf("####### FAIL : AHB RECEIVED WRONG DATA from %s", slave_cfg.name))
          `uvm_info("SCRBD", $sformatf("expected = %h, received = %h", temp1, transfer.data), UVM_MEDIUM)
        end
      end
  endfunction : write_ahb
   
  function void assign_csr(spi_pkg::spi_csr_s csr_setting);
    csr = csr_setting;
  endfunction : assign_csr

endclass : spi2ahb_scbd

class ahb2spi_scbd extends uvm_scoreboard;
  bit [7:0] data_from_ahb[$];

  bit [7:0] temp1;
  bit [7:0] mask;

  spi_pkg::spi_csr_s csr;
  apb_pkg::apb_slave_config slave_cfg;

  `uvm_component_utils(ahb2spi_scbd)
  uvm_analysis_imp_ahb #(ahb_pkg::ahb_transfer, ahb2spi_scbd) ahb_add;
  uvm_analysis_imp_spi #(spi_pkg::spi_transfer, ahb2spi_scbd) spi_match;
   
  function new (string name = "", uvm_component parent = null);
    super.new(name, parent);
    spi_match = new("spi_match", this);
    ahb_add    = new("ahb_add", this);
  endfunction : new
   
  // implement AHB WRITE analysis port from reference model
  virtual function void write_ahb(input ahb_pkg::ahb_transfer transfer);
    if ((transfer.address ==  (slave_cfg.start_address + `SPI_TX0_REG)) && (transfer.direction.name() == "WRITE")) 
        data_from_ahb.push_back(transfer.data[7:0]);
  endfunction : write_ahb
   
  // implement SPI Rx analysis port from reference model
  virtual function void write_spi( spi_pkg::spi_transfer transfer);
    mask = calc_mask();
    temp1 = data_from_ahb.pop_front();

    if ((temp1 & mask) == transfer.receive_data[7:0])
      `uvm_info("SCRBD", $sformatf("####### PASS : %s RECEIVED CORRECT DATA expected = %h, received = %h", slave_cfg.name, (temp1 & mask), transfer.receive_data), UVM_MEDIUM)
    else begin
      `uvm_error(get_type_name(), $sformatf("####### FAIL : %s RECEIVED WRONG DATA", slave_cfg.name))
      `uvm_info("SCRBD", $sformatf("expected = %h, received = %h", temp1, transfer.receive_data), UVM_MEDIUM)
    end
  endfunction : write_spi
   
  function void assign_csr(spi_pkg::spi_csr_s csr_setting);
     csr = csr_setting;
  endfunction : assign_csr
   
  function bit[31:0] calc_mask();
    case (csr.data_size)
      8: return 32'h00FF;
      16: return 32'h00FFFF;
      24: return 32'h00FFFFFF;
      32: return 32'hFFFFFFFF;
      default: return 8'hFF;
    endcase
  endfunction : calc_mask

endclass : ahb2spi_scbd

