//File name   : dma_ahb_master.v
//Title       : 
//Created     : 1999
//Description : DMA ahb master control
//Notes       : The DMA AHB master will gain control of the AHb interface when 
//              requested by the DMA arbiter.The request is removed under control 
//	        of the arbiter - this may either force only single transfers or 
// 	        allow the channel to control the transfer length.
//Limitations : Not currently compatible with slaves that issue retry/split
//              responses 
//----------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// Include Files
//------------------------------------------------------------------------------

`include   "dma_defs.v"             // DMA defines

//------------------------------------------------------------------------------
// Module Declaration
//------------------------------------------------------------------------------
// 
module dma_ahb_master(
                hclk,
                n_hreset,
                hready,
                hgrant,
                hbusreq,
                hlock,
                ahb_request,
                addr_drive,
                data_drive
                );

//==================
// Port Declarations
//==================

  input         hclk;
  input         n_hreset;
  input         hready;
  input         hgrant;
  output        hbusreq;
  output        hlock;
  input         ahb_request;
  output        addr_drive;
  output        data_drive;

//====================
// Signal declarations
//====================

  wire          hclk;
  wire          n_hreset;
  wire          hready;
  wire          hgrant;
  wire          ahb_request;

  wire          hbusreq;
  wire          hlock;
  reg           addr_drive;
  reg           data_drive;
  reg     [1:0] grant_state;
  reg     [1:0] next_grant_state;


//==========
// Main code
//==========

// Next state logic

always @(grant_state or hready or hgrant)
begin
    next_grant_state = grant_state;
    if (hready)
        case (grant_state)
        `not_granted :
            if (hgrant)
                next_grant_state = `initial_grant;
            else
                next_grant_state = `not_granted;
        `initial_grant :
            if (hgrant)
                next_grant_state = `grant;
            else
                next_grant_state = `final_grant;
        `grant :
            if (hgrant)
                next_grant_state = `grant;
            else
                next_grant_state = `final_grant;
        `final_grant :
            if (hgrant)
                next_grant_state = `initial_grant;
            else
                next_grant_state = `not_granted;
        default :
            next_grant_state = `not_granted;
        endcase
end

// State switch logic

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        grant_state <= `not_granted;
    else
        grant_state <= next_grant_state;
end

// generate address and data drive lines - if required
// These can be output and the channels can use them if required.
// The channels can use them to remove the request lines to the arbiter
// and hence allow the AHB arbiter to grant a different master.

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        addr_drive <= 1'b0;
        data_drive <= 1'b0;
    end
    else
    begin
        if ((next_grant_state == `initial_grant) | (next_grant_state == `grant))
            addr_drive <= 1'b1;
        else
            addr_drive <= 1'b0;
        if ((next_grant_state == `grant) | (next_grant_state == `final_grant))
            data_drive <= 1'b1;
        else
            data_drive <= 1'b0;
    end
end

// Request logic is contained in the arbiter
  assign hbusreq = ahb_request;

// default drives - these will be channel specific enabling new channels to 
// be written with capability to perform range of accesses (locked etc.)

// asume locked cycles can not occur
  assign hlock = 1'b0;

endmodule

