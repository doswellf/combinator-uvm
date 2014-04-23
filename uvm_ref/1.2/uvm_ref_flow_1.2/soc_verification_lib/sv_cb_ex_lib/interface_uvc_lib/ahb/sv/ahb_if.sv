// IVB checksum: 876316374
/*-----------------------------------------------------------------
File name     : ahb_if.sv
Created       : Wed May 19 15:42:20 2010
Description   :
Notes         :
-----------------------------------------------------------------*/
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


interface ahb_if (input ahb_clock, input ahb_resetn );

  // Import UVM package
  import uvm_pkg::*;

  /***************************************************************************
   IVB-NOTE : REQUIRED : OVC signal definitions : signals definitions
   -------------------------------------------------------------------------
   Adjust the signal names and add any necessary signals.
   Note that if you change a signal name, you must change it in all of your
   OVC files.
   ***************************************************************************/


   // Clock source (in)
   logic AHB_HCLK;
   // Transfer kind (out)
   logic [1:0] AHB_HTRANS;
   // Burst kind (out)
   logic [2:0] AHB_HBURST;
   // Transfer size (out)
   logic [2:0] AHB_HSIZE;
   // Transfer direction (out)
   logic AHB_HWRITE;
   // Protection control (out)
   logic [3:0] AHB_HPROT;
   // Address bus (out)
   logic [`AHB_ADDR_WIDTH-1:0] AHB_HADDR;
   // Write data bus (out)
   logic [`AHB_DATA_WIDTH-1:0] AHB_HWDATA;
   // Read data bus (in)
   logic [`AHB_DATA_WIDTH-1:0] AHB_HRDATA;
   // Bus grant (in)
   logic AHB_HGRANT;
   // Slave is ready (in)
   logic AHB_HREADY;
   // Locked transfer request (out)
   logic AHB_HLOCK;
   // Bus request	(out)
   logic AHB_HBUSREQ;
   // Reset (in)
   logic AHB_HRESET;
   // Transfer response (in)
   logic [1:0] AHB_HRESP;

  
  // Control flags
  bit has_checks = 1;
  bit has_coverage = 1;

  // Coverage and assertions to be implemented here
  /***************************************************************************
   IVB-NOTE : REQUIRED : Assertion checks : Interface
   -------------------------------------------------------------------------
   Add assertion checks as required.
   ***************************************************************************/

  // SVA default clocking
  wire uvm_assert_clk = ahb_clock && has_checks;
  default clocking master_clk @(negedge uvm_assert_clk);
  endclocking

  // SVA Default reset
  default disable iff (ahb_resetn);


endinterface : ahb_if

