//File name   : dma_ahb_mux.v
//Title       : 
//Created     : 1999
//Description : DMA ahb mux
//Notes       : The DMA ahb mux takes the bus signals from
//              the various channels and selects the correct
//              channel to be output to the central AHB mux.
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

//------------------------------------------------------------------------------
// Include Files
//------------------------------------------------------------------------------
`include   "dma_defs.v"             // DMA defines

//------------------------------------------------------------------------------
// Module Declaration
//------------------------------------------------------------------------------
// 
module dma_ahb_mux(
                hclk,        //commented by Binata
                n_hreset,     //commented by Binata
                hready_in,
                haddr,
                htrans,
                hwrite,
                hsize,
                hburst,
                hprot,
                hwdata,
                hrdata,
                //addr_drive,commented by Binata
                //data_drive,commented by Binata
`ifdef one_channel
`else
                // channel 1 connections
                ch1_ahb_grant,
                ch1_haddr,
                ch1_htrans,
                ch1_hwrite,
                ch1_hsize,
                ch1_hburst,
                ch1_hprot,
                ch1_hwdata,
                ch1_hrdata,
`ifdef two_channel
`else
                // channel 2 connections
                ch2_ahb_grant,
                ch2_haddr,
                ch2_htrans,
                ch2_hwrite,
                ch2_hsize,
                ch2_hburst,
                ch2_hprot,
                ch2_hwdata,
                ch2_hrdata,
`ifdef three_channel
`else
                // channel 3 connections
                ch3_ahb_grant,
                ch3_haddr,
                ch3_htrans,
                ch3_hwrite,
                ch3_hsize,
                ch3_hburst,
                ch3_hprot,
                ch3_hwdata,
                ch3_hrdata,
`endif
`endif
`endif
                // channel 0 connections
                ch0_ahb_grant,
                ch0_haddr,
                ch0_htrans,
                ch0_hwrite,
                ch0_hsize,
                ch0_hburst,
                ch0_hprot,
                ch0_hwdata,
                ch0_hrdata
                );

//==================
// Port declarations
//==================

  input         hclk;
  input         n_hreset;
  input         hready_in;
  output [31:0] haddr;
  output  [1:0] htrans;
  output        hwrite;
  output  [2:0] hsize;
  output  [2:0] hburst;
  output  [3:0] hprot;
  output [31:0] hwdata;
  input  [31:0] hrdata;

  //input         addr_drive;
  //input         data_drive;

  input         ch0_ahb_grant;
  input  [31:0] ch0_haddr;
  input   [1:0] ch0_htrans;
  input         ch0_hwrite;
  input   [2:0] ch0_hsize;
  input   [2:0] ch0_hburst;
  input   [3:0] ch0_hprot;
  input  [31:0] ch0_hwdata;
  output [31:0] ch0_hrdata;
`ifdef one_channel
`else
  input         ch1_ahb_grant;
  input  [31:0] ch1_haddr;
  input   [1:0] ch1_htrans;
  input         ch1_hwrite;
  input   [2:0] ch1_hsize;
  input   [2:0] ch1_hburst;
  input   [3:0] ch1_hprot;
  input  [31:0] ch1_hwdata;
  output [31:0] ch1_hrdata;
`ifdef two_channel
`else
  input         ch2_ahb_grant;
  input  [31:0] ch2_haddr;
  input   [1:0] ch2_htrans;
  input         ch2_hwrite;
  input   [2:0] ch2_hsize;
  input   [2:0] ch2_hburst;
  input   [3:0] ch2_hprot;
  input  [31:0] ch2_hwdata;
  output [31:0] ch2_hrdata;
`ifdef three_channel
`else
  input         ch3_ahb_grant;
  input  [31:0] ch3_haddr;
  input   [1:0] ch3_htrans;
  input         ch3_hwrite;
  input   [2:0] ch3_hsize;
  input   [2:0] ch3_hburst;
  input   [3:0] ch3_hprot;
  input  [31:0] ch3_hwdata;
  output [31:0] ch3_hrdata;
`endif
`endif
`endif

//====================
// signal declarations
//====================

  //wire          hclk;
  //wire          hresetn;
  reg    [31:0] haddr;
  reg     [1:0] htrans;
  reg           hwrite;
  reg     [2:0] hsize;
  reg     [2:0] hburst;
  reg     [3:0] hprot;
  reg    [31:0] hwdata;
  wire   [31:0] hrdata;

  //wire          addr_drive;
  //wire          data_drive;

  wire          ch0_ahb_grant;
  wire   [31:0] ch0_haddr;
  wire    [1:0] ch0_htrans;
  wire          ch0_hwrite;
  wire    [2:0] ch0_hsize;
  wire    [2:0] ch0_hburst;
  wire    [3:0] ch0_hprot;
  wire   [31:0] ch0_hwdata;
  reg    [31:0] ch0_hrdata;
`ifdef one_channel
`else
  wire          ch1_ahb_grant;
  wire   [31:0] ch1_haddr;
  wire    [1:0] ch1_htrans;
  wire          ch1_hwrite;
  wire    [2:0] ch1_hsize;
  wire    [2:0] ch1_hburst;
  wire    [3:0] ch1_hprot;
  wire   [31:0] ch1_hwdata;
  reg    [31:0] ch1_hrdata;
`ifdef two_channel
`else
  wire          ch2_ahb_grant;
  wire   [31:0] ch2_haddr;
  wire    [1:0] ch2_htrans;
  wire          ch2_hwrite;
  wire    [2:0] ch2_hsize;
  wire    [2:0] ch2_hburst;
  wire    [3:0] ch2_hprot;
  wire   [31:0] ch2_hwdata;
  reg    [31:0] ch2_hrdata;
`ifdef three_channel
`else
  wire          ch3_ahb_grant;
  wire   [31:0] ch3_haddr;
  wire    [1:0] ch3_htrans;
  wire          ch3_hwrite;
  wire    [2:0] ch3_hsize;
  wire    [2:0] ch3_hburst;
  wire    [3:0] ch3_hprot;
  wire   [31:0] ch3_hwdata;
  reg    [31:0] ch3_hrdata;
`endif
`endif
`endif

  reg     [3:0] channel_addr;
  reg     [3:0] channel_addr_data;


//==========
// Main code
//==========

// This module is basically a number of muxes - the address and control
// muxes are driven when addr_drive is asserted with the selection being 
// made using the grant signals and a delayed version of these.  The data 
// is driven when the data_drive is asserted with the selection again being 
// made on the grant signals with further delayed versions being used as required

// need to generate delayed versions of the channel grant signals to ensure the 
// correct channel is granted the bus.

`ifdef one_channel
always @(ch0_ahb_grant)
`else
`ifdef two_channel
always @(ch0_ahb_grant or ch1_ahb_grant)
`else
`ifdef three_channel
always @(ch0_ahb_grant or ch1_ahb_grant or ch2_ahb_grant)
`else
always @(ch0_ahb_grant or ch1_ahb_grant or ch2_ahb_grant or ch3_ahb_grant)
`endif
`endif
`endif
begin
`ifdef one_channel
    channel_addr = {3'b000, ch0_ahb_grant};
//Binata
`else `ifdef two_channel
//`elseif two_channel
    channel_addr = {2'b00, ch1_ahb_grant, ch0_ahb_grant};
`else `ifdef three_channel
//`elseif three_channel
    channel_addr = {1'b0, ch2_ahb_grant, 
                    ch1_ahb_grant, ch0_ahb_grant};

`else
    channel_addr = {ch3_ahb_grant, ch2_ahb_grant, 
                    ch1_ahb_grant, ch0_ahb_grant};
`endif
`endif
`endif
end

// address and control mux - use channel_addr as a selector should only be 
// valid when address is driven

always @(ch0_haddr or ch0_htrans or ch0_hwrite or ch0_hsize or ch0_hburst or
            ch0_hprot or
`ifdef one_channel
`else
         ch1_haddr or ch1_htrans or ch1_hwrite or ch1_hsize or ch1_hburst or
            ch1_hprot or 
`ifdef two_channel
`else
         ch2_haddr or ch2_htrans or ch2_hwrite or ch2_hsize or ch2_hburst or
            ch2_hprot or 
`ifdef three_channel
`else
         ch3_haddr or ch3_htrans or ch3_hwrite or ch3_hsize or ch3_hburst or
            ch3_hprot or 
`endif
`endif
`endif
         channel_addr)
begin
    case (channel_addr)
        `ch0_selected :
        begin
            haddr = ch0_haddr;
            htrans = ch0_htrans;
            hwrite = ch0_hwrite;
            hsize = ch0_hsize;
            hburst = ch0_hburst;
            hprot = ch0_hprot;
        end
`ifdef one_channel
`else
        `ch1_selected :
        begin
            haddr = ch1_haddr;
            htrans = ch1_htrans;
            hwrite = ch1_hwrite;
            hsize = ch1_hsize;
            hburst = ch1_hburst;
            hprot = ch1_hprot;
        end
`ifdef two_channel
`else
        `ch2_selected :
        begin
            haddr = ch2_haddr;
            htrans = ch2_htrans;
            hwrite = ch2_hwrite;
            hsize = ch2_hsize;
            hburst = ch2_hburst;
            hprot = ch2_hprot;
        end    
`ifdef three_channel
`else
        `ch3_selected :
        begin
            haddr = ch3_haddr;
            htrans = ch3_htrans;
            hwrite = ch3_hwrite;
            hsize = ch3_hsize;
            hburst = ch3_hburst;
            hprot = ch3_hprot;
        end    
`endif
`endif
`endif
        default :
        begin
            haddr = 32'h00000000;
            htrans = 2'b00;
            hwrite = 1'b0;
            hsize = 3'b000;
            hburst = 3'b000;
            hprot = 4'b0000;
        end
    endcase
end

// Register channel_addr to control the data
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        channel_addr_data <= 4'b0;
    else if (hready_in)
        channel_addr_data <= channel_addr;
end

// Data mux - use channel data as selector

always @(ch0_hwdata or 
`ifdef one_channel
`else
         ch1_hwdata or 
`ifdef two_channel
`else
         ch2_hwdata or 
`ifdef three_channel
`else
         ch3_hwdata or 
`endif
`endif
`endif
         channel_addr_data)
begin
    case (channel_addr_data)
        `ch0_selected :
            hwdata = ch0_hwdata;
`ifdef one_channel
`else
        `ch1_selected :
            hwdata = ch1_hwdata;
`ifdef two_channel
`else
        `ch2_selected :
            hwdata = ch2_hwdata;
`ifdef three_channel
`else
        `ch3_selected :
            hwdata = ch3_hwdata;
`endif
`endif
`endif
        default :
            hwdata = 32'h00000000;
    endcase
end

// read data is just sent to each channel

always @(hrdata)
begin
    ch0_hrdata = hrdata;
`ifdef one_channel
`else
    ch1_hrdata = hrdata;
`ifdef two_channel
`else
    ch2_hrdata = hrdata;
`ifdef three_channel
`else
    ch3_hrdata = hrdata;
`endif
`endif
`endif
end

endmodule
