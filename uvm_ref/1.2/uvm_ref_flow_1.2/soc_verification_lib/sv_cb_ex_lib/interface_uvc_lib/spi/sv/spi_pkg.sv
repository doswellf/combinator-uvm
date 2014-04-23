/*-------------------------------------------------------------------------
File name   : spi_pkg.sv
Title       : Package for SPI OVC
Project     :
Created     :
Description : 
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

  
`ifndef SPI_PKG_SVH
`define SPI_PKG_SVH

package spi_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

//////////////////////////////////////////////////
//        UVM Class Forward Declarations        //
//////////////////////////////////////////////////

typedef class spi_agent;
typedef class spi_csr;
typedef class spi_driver;
typedef class spi_env;
typedef class spi_monitor;
typedef class trans_seq;
typedef class spi_incr_payload;
typedef class spi_sequencer;
typedef class spi_transfer;

//////////////////////////////////////////////////
//              Include files                   //
//////////////////////////////////////////////////
`include "spi_csr.sv"
`include "spi_transfer.sv"
`include "spi_config.sv"

`include "spi_monitor.sv"
`include "spi_sequencer.sv"
`include "spi_driver.sv"
`include "spi_agent.sv"

`include "spi_env.sv"

`include "spi_seq_lib.sv"

endpackage : spi_pkg
`endif
