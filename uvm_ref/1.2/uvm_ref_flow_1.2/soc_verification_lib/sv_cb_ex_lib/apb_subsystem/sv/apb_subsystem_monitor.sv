/*-------------------------------------------------------------------------
File name   : apb_subsystem_monitor.sv
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

class apb_subsystem_monitor extends uvm_monitor; 

  spi2ahb_scbd tx_scbd;
  ahb2spi_scbd rx_scbd;
   
  uvm_analysis_imp#(spi_pkg::spi_csr, apb_subsystem_monitor) dut_csr_port_in;

  `uvm_component_utils(apb_subsystem_monitor)

  // constructor
  function new(input string name, input uvm_component parent=null);
    super.new(name,parent);
    dut_csr_port_in = new("dut_csr_port_in", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // build scoreboard
    tx_scbd = spi2ahb_scbd::type_id::create("tx_scbd",this);
    rx_scbd = ahb2spi_scbd::type_id::create("rx_scbd",this);

  endfunction : build_phase
  
  // pass csr_setting to scoreboard and coverage
  function void write(spi_pkg::spi_csr csr_setting);
    tx_scbd.assign_csr(csr_setting.csr_s);
    rx_scbd.assign_csr(csr_setting.csr_s);
  endfunction

  function void set_slave_config(apb_pkg::apb_slave_config slave_cfg);
    tx_scbd.slave_cfg = slave_cfg;
    rx_scbd.slave_cfg = slave_cfg;
  endfunction

endclass : apb_subsystem_monitor

