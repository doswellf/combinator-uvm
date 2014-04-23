/*-------------------------------------------------------------------------
File name   : gpio_if.sv
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


interface gpio_if();

  // Control flags
  bit                has_checks = 1;
  bit                has_coverage = 1;

  // Actual Signals
  // APB Slave Interface - inputs
  logic              pclk;
  logic              n_p_reset;

  // Slave GPIO Interface - inputs
  logic [`GPIO_DATA_WIDTH-1:0]       n_gpio_pin_oe;
  logic [`GPIO_DATA_WIDTH-1:0]       gpio_pin_out;
  logic [`GPIO_DATA_WIDTH-1:0]       gpio_pin_in;

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

endinterface : gpio_if

