//File name   : dma_apb_mux.v
//Title       : 
//Created     : 1999
//Description : DMA apb mux
//Notes       : The DMA apb mux takes the bus signals from the various channels and
//              selects the correct channel to be output to the APB bridge.
//              Each of the channels will generate correct apb signals with the
//              outputs being asserted as soon as the flow control is enabled.
//              The mux will then pass the correct signals to the bridge. If an 
//              access is unable to complete immediately (ARM has the bus!) 
//              the channel will hold (using the pready signal?) until the access 
//              can complete.  If after 32 clocks the access is still held abort..
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
module dma_apb_mux(
            //hclk, commented by Binata
            //hresetn,commented by Binata                    
            // apb interface master signals
            dma_penable,
            dma_pwrite,
            dma_paddr,
            dma_pwdata,
            byte_access,
            prdata,
            pready,
            // channel apb bus signals
`ifdef one_channel
`else
            ch1_penable,
            ch1_pwrite,
            ch1_paddr,
            ch1_pwdata,
            ch1_byte_access,
            prdata_ch1,
            pready_ch1,
            // channel grant signal
            ch1_apb_grant,
`ifdef two_channel
`else
            ch2_penable,
            ch2_pwrite,
            ch2_paddr,
            ch2_pwdata,
            ch2_byte_access,
            prdata_ch2,
            pready_ch2,
            // channel grant signal
            ch2_apb_grant,
`ifdef three_channel
`else
            ch3_penable,
            ch3_pwrite,
            ch3_paddr,
            ch3_pwdata,
            ch3_byte_access,
            prdata_ch3,
            pready_ch3,
            // channel grant signal
            ch3_apb_grant,
`endif
`endif
`endif
            ch0_penable,
            ch0_pwrite,
            ch0_paddr,
            ch0_pwdata,
            ch0_byte_access,
            prdata_ch0,
            pready_ch0,
            // channel grant signal
            ch0_apb_grant
            );

//==========================
// input/output declarations
//==========================

  //input             hclk;
  //input             hresetn;
// apb interface master signals
  input    [15:0]   prdata;
  input             pready;
  output            dma_penable;
  output            dma_pwrite;
  output   [19:0]   dma_paddr;
  output   [15:0]   dma_pwdata;
  output            byte_access;
// channel apb bus signals
  input             ch0_penable;
  input             ch0_pwrite;
  input    [19:0]   ch0_paddr;
  input    [15:0]   ch0_pwdata;
  input             ch0_byte_access;
  output   [15:0]   prdata_ch0;
  output            pready_ch0;
// channel grant signal
  input             ch0_apb_grant;
`ifdef one_channel
`else
  input             ch1_penable;
  input             ch1_pwrite;
  input    [19:0]   ch1_paddr;
  input    [15:0]   ch1_pwdata;
  input             ch1_byte_access;
  output   [15:0]   prdata_ch1;
  output            pready_ch1;
// channel grant signal
  input             ch1_apb_grant;
`ifdef two_channel
`else
  input             ch2_penable;
  input             ch2_pwrite;
  input    [19:0]   ch2_paddr;
  input    [15:0]   ch2_pwdata;
  input             ch2_byte_access;
  output   [15:0]   prdata_ch2;
  output            pready_ch2;
// channel grant signal
  input             ch2_apb_grant;
`ifdef three_channel
`else
  input             ch3_penable;
  input             ch3_pwrite;
  input    [19:0]   ch3_paddr;
  input    [15:0]   ch3_pwdata;
  input             ch3_byte_access;
  output   [15:0]   prdata_ch3;
  output            pready_ch3;
// channel grant signal
  input             ch3_apb_grant;
`endif
`endif
`endif

//==================
// wire declarations
//==================

  //wire              hclk;
  //wire              hresetn;
// apb interface master signals
  wire     [15:0]   prdata;
  wire              pready;
  reg               dma_penable;
  reg               dma_pwrite;
  reg      [19:0]   dma_paddr;
  reg      [15:0]   dma_pwdata;
  reg               byte_access;
// channel apb bus signals
  wire              ch0_penable;
  wire              ch0_pwrite;
  wire     [19:0]   ch0_paddr;
  wire     [15:0]   ch0_pwdata;
  wire              ch0_byte_access;
  reg      [15:0]   prdata_ch0;
  reg               pready_ch0;
// channel grant signal
  wire              ch0_apb_grant;
`ifdef one_channel
`else
  wire              ch1_penable;
  wire              ch1_pwrite;
  wire     [19:0]   ch1_paddr;
  wire     [15:0]   ch1_pwdata;
  wire              ch1_byte_access;
  reg      [15:0]   prdata_ch1;
  reg               pready_ch1;
// channel grant signal
  wire              ch1_apb_grant;
`ifdef two_channel
`else
  wire              ch2_penable;
  wire              ch2_pwrite;
  wire     [19:0]   ch2_paddr;
  wire     [15:0]   ch2_pwdata;
  wire              ch2_byte_access;
  reg      [15:0]   prdata_ch2;
  reg               pready_ch2;
// channel grant signal
  wire              ch2_apb_grant;
`ifdef three_channel
`else
  wire              ch3_penable;
  wire              ch3_pwrite;
  wire     [19:0]   ch3_paddr;
  wire     [15:0]   ch3_pwdata;
  wire              ch3_byte_access;
  reg      [15:0]   prdata_ch3;
  reg               pready_ch3;
// channel grant signal
  wire              ch3_apb_grant;
`endif
`endif
`endif


//==========
// Main code
//==========

// Mux to control main apb outputs - it isn't possible for more than one channel
// to be granted at any one time)

always @(
`ifdef one_channel
`else
        ch1_apb_grant or ch1_penable or ch1_pwrite or ch1_paddr or
        ch1_pwdata or ch1_byte_access or
`ifdef two_channel
`else
        ch2_apb_grant or ch2_penable or ch2_pwrite or ch2_paddr or
        ch2_pwdata or ch2_byte_access or
`ifdef three_channel
`else
        ch3_apb_grant or ch3_penable or ch3_pwrite or ch3_paddr or
        ch3_pwdata or ch3_byte_access or
`endif
`endif
`endif
        ch0_apb_grant or ch0_penable or ch0_pwrite or ch0_paddr or
        ch0_pwdata or ch0_byte_access)
begin
    case ({ch0_apb_grant, 
`ifdef one_channel
           3'b000})
`else
           ch1_apb_grant, 
`ifdef two_channel
           2'b00})
`else
           ch2_apb_grant, 
`ifdef three_channel
           1'b0})
`else
           ch3_apb_grant})
`endif
`endif
`endif
        `channel0 :
        begin
            dma_penable = ch0_penable;
            dma_pwrite  = ch0_pwrite;
            dma_paddr   = ch0_paddr;
            dma_pwdata  = ch0_pwdata;
            byte_access = ch0_byte_access;
        end
`ifdef one_channel
`else
        `channel1 :
        begin
            dma_penable = ch1_penable;
            dma_pwrite  = ch1_pwrite;
            dma_paddr   = ch1_paddr;
            dma_pwdata  = ch1_pwdata;
            byte_access = ch1_byte_access;
        end
`ifdef two_channel
`else
        `channel2 :
        begin
            dma_penable = ch2_penable;
            dma_pwrite  = ch2_pwrite;
            dma_paddr   = ch2_paddr;
            dma_pwdata  = ch2_pwdata;
            byte_access = ch2_byte_access;
        end        
`ifdef three_channel
`else
        `channel3 :
        begin
            dma_penable = ch3_penable;
            dma_pwrite  = ch3_pwrite;
            dma_paddr   = ch3_paddr;
            dma_pwdata  = ch3_pwdata;
            byte_access = ch3_byte_access;
        end       
`endif
`endif
`endif 
        default :
        begin
            dma_penable = 1'b0;
            dma_pwrite  = 1'b0;
            dma_paddr   = 20'h00000;
            dma_pwdata  = 16'h0000;
            byte_access = 1'b0;
        end
    endcase
end

// Mux for read data back to channels - all see the same

always @(prdata)
begin
    prdata_ch0 = prdata;
`ifdef one_channel
`else
    prdata_ch1 = prdata;
`ifdef two_channel
`else
    prdata_ch2 = prdata;
`ifdef three_channel
`else
    prdata_ch3 = prdata;
`endif
`endif
`endif 
end

// Mux for pready - only want this to be used by relevant channels

always @(pready or 
`ifdef one_channel
`else
         ch1_apb_grant or 
`ifdef two_channel
`else
         ch2_apb_grant or 
`ifdef three_channel
`else
         ch3_apb_grant or 
`endif
`endif
`endif 
         ch0_apb_grant)
begin
    pready_ch0 = 1'b0;
`ifdef one_channel
`else
    pready_ch1 = 1'b0;
`ifdef two_channel
`else
    pready_ch2 = 1'b0;
`ifdef three_channel
`else
    pready_ch3 = 1'b0;
`endif
`endif
`endif 

    if (ch0_apb_grant)
        pready_ch0 = pready;
`ifdef one_channel
`else
    else if (ch1_apb_grant)
        pready_ch1 = pready;
`ifdef two_channel
`else
    else if (ch2_apb_grant)
        pready_ch2 = pready;
`ifdef three_channel
`else
    else if (ch3_apb_grant)
        pready_ch3 = pready;
`endif
`endif
`endif 
    
end

endmodule
