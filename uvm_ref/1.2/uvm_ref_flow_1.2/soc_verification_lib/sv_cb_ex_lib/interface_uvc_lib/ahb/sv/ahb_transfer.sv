// IVB checksum: 2173772784
/*-----------------------------------------------------------------
File name     : ahb_transfer.sv
Created       : Wed May 19 15:42:20 2010
Description   :  This file declares the OVC transfer. It is
              :  used by both master and slave.
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


`ifndef AHB_TRANSFER_SV
`define AHB_TRANSFER_SV

//------------------------------------------------------------------------------
//
// ahb transfer enums, parameters, and events
//
//------------------------------------------------------------------------------

typedef enum logic[2:0]  {
		BYTE = 0,
		HALFWORD = 1,
		WORD = 2,
		TWO_WORDS = 3,
		FOUR_WORDS = 4,
		EIGHT_WORDS = 5,
		SIXTEEN_WORDS = 6,
		K_BITS = 7
} ahb_transfer_size;
typedef enum logic[1:0]  {
		IDLE = 0,
		BUSY = 1,
		NONSEQ = 2,
		SEQ = 3
} ahb_transfer_kind;
typedef enum logic[1:0]  {
		OKAY = 0,
		ERROR = 1,
		RETRY = 2,
		SPLIT = 3
} ahb_response_kind;
typedef enum logic  {
		READ = 0,
		WRITE = 1
} ahb_direction;
typedef enum logic[2:0]  {
		SINGLE = 0,
		INCR = 1,
		WRAP4 = 2,
		INCR4 = 3,
		WRAP8 = 4,
		INCR8 = 5,
		WRAP16 = 6,
		INCR16 = 7
} ahb_burst_kind;
 
//------------------------------------------------------------------------------
//
// CLASS: ahb_transfer
//
//------------------------------------------------------------------------------

class ahb_transfer extends uvm_sequence_item;

  /***************************************************************************
   IVB-NOTE : REQUIRED : transfer definitions : Item definitions
   ---------------------------------------------------------------------------
   Adjust the transfer attribute names as required and add any 
   necessary attributes.
   Note that if you change an attribute name, you must change it in all of your
   OVC files.
   Make sure to edit the uvm_object_utils_begin to get various utilities (like
   print and copy) for each attribute that you add.
  ***************************************************************************/           
  rand logic [`AHB_DATA_WIDTH-1:0] data;
  rand logic [`AHB_ADDR_WIDTH-1:0] address;
  rand ahb_direction direction ;
  rand ahb_transfer_size  hsize;
  rand ahb_burst_kind  burst;
  rand logic [3:0] prot ;
 
  `uvm_object_utils_begin(ahb_transfer)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(address, UVM_ALL_ON)
    `uvm_field_enum(ahb_direction,direction, UVM_ALL_ON)
    `uvm_field_enum(ahb_transfer_size,hsize, UVM_ALL_ON)
    `uvm_field_enum(ahb_burst_kind,burst, UVM_ALL_ON)
    `uvm_field_int(prot, UVM_ALL_ON)
  `uvm_object_utils_end


  // Constructor - required syntax for UVM automation and utilities
  function new (string name = "unnamed-ahb_transfer");
    super.new(name);
  endfunction : new

endclass : ahb_transfer

`endif // AHB_TRANSFER_SV

