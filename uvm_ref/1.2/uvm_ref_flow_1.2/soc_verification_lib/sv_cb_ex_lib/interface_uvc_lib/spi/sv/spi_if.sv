/*-------------------------------------------------------------------------
File name   : spi_if.sv
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


interface spi_if();

  // Control flags
  bit                has_checks = 1;
  bit                has_coverage = 1;

  // Actual Signals
  // APB Slave Interface - inputs
  logic              sig_pclk;
  logic              sig_n_p_reset;

  // Slave SPI Interface - inputs
  logic              sig_si;                //MOSI, Slave input
  logic              sig_sclk_in;
  logic              sig_n_ss_in;
  logic              sig_slave_in_clk;
  // Slave SPI Interface - outputs
  logic              sig_slave_out_clk;
  logic              sig_n_so_en;          //MISO, Output enable
  logic              sig_so;               //MISO, Slave output


  // Master SPI Interface - inputs
  logic              sig_mi;               //MISO, Master input
  logic              sig_ext_clk;
  // Master SPI Interface - outputs
  logic              sig_n_ss_en;
  logic        [3:0] sig_n_ss_out;
  logic              sig_n_sclk_en;
  logic              sig_sclk_out;
  logic              sig_n_mo_en;          //MOSI, Output enable
  logic              sig_mo;               //MOSI, Master input

// Coverage and assertions to be implemented here.

/*
always @(negedge sig_pclk)
begin

// Read and write never true at the same time
assertReadOrWrite: assert property (
                   disable iff(!has_checks) 
                   ($onehot(sig_grant) |-> !(sig_read && sig_write)))
                   else
                     $error("ERR_READ_OR_WRITE\n Read and Write true at \
                             the same time");

end
*/

endinterface : spi_if

