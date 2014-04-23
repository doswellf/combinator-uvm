/******************************************************************************

  FILE : apb_slave_if.sv

 ******************************************************************************/
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


interface apb_slave_if(input pclock, preset);
  // Actual Signals
   parameter         PADDR_WIDTH  = 32;
   parameter         PWDATA_WIDTH = 8;
   parameter         PRDATA_WIDTH = PWDATA_WIDTH;

  // Control flags
  bit                has_checks = 1;
  bit                has_coverage = 1;

  // Actual Signals
  //wire logic              pclock;
  //wire logic              preset;
  wire logic       [PADDR_WIDTH-1:0] paddr;
  wire logic              prwd;
  wire logic       [PWDATA_WIDTH-1:0] pwdata;
  wire logic              psel;
  wire logic              penable;

  logic        [PRDATA_WIDTH-1:0] prdata;
  logic              pslverr;
  logic              pready;

  // Coverage and assertions to be implegmented here.

/*  fix to make concurrent assertions
always @(posedge pclock)
begin

// Pready must not be X or Z
assertPreadyUnknown:assert property (
                  disable iff(!has_checks) 
                  (!($isunknown(pready))))
                  else
                    $error("ERR_APB100_PREADY_XZ\n Pready went to X or Z");


// Pslverr must not be X or Z
assertPslverrUnknown:assert property (
                  disable iff(!has_checks) 
                  ((psel == 1'b0 or pready == 1'b0 or !($isunknown(pslverr)))))
                  else  
                    $error("ERR_APB101_PSLVERR_XZ\n Pslverr went to X or Z when responding");


// Prdata must not be X or Z
assertPrdataUnknown:assert property (
                  disable iff(!has_checks) 
                  ((psel == 1'b0 or pready == 0 or prwd == 0 or !($isunknown(prdata)))))
                  else
                  $error("ERR_APB102_XZ\n Prdata went to X or Z when responding to a read transfer");



end

   // EACH SLAVE HAS ITS OWN PSEL LINES FOR WHICH THE APB ABV VIP Checker can be run on.
`include "apb_checker.sv"
*/

endinterface : apb_slave_if

