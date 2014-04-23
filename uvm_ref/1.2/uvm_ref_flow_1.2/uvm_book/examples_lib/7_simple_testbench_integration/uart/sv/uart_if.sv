/*-------------------------------------------------------------------------
File name   : uart_if.sv
Title       : Interface file for uart uvc
Project     :
Created     :
Description : Defines UART Interface
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

  
interface uart_if(input clock, reset);

  logic txd;    // Transmit Data
  logic rxd;    // Receive Data
  
  logic intrpt;  // Interrupt

  logic ri_n;    // ring indicator
  logic cts_n;   // clear to send
  logic dsr_n;   // data set ready
  logic rts_n;   // request to send
  logic dtr_n;   // data terminal ready
  logic dcd_n;   // data carrier detect

  logic baud_clk;  // Baud Rate Clock
  
  // Control flags
  bit                has_checks = 1;
  bit                has_coverage = 1;

/*  FIX TO USE CONCURRENT ASSERTIONS
  always @(posedge clock)
  begin
    // rxd must not be X or Z
    assertRxdUnknown:assert property (
                       disable iff(!has_checks || !reset)(!$isunknown(rxd)))
                       else
                         $error("ERR_UART001_Rxd_XZ\n Rxd went to X or Z");
  end
*/

endinterface : uart_if
