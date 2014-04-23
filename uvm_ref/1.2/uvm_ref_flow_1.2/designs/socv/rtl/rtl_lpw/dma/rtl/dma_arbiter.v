//File name   : dma_arbiter.v
//Title       : 
//Created     : 1999
//Description : DMA arbiter
//Notes       :  The DMA arbiter takes the request lines from the various channels
//               and grants them in a round robin fashion.  In the case of
//               ahb requests it first obtains the ahb bus before issueing the grant.
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
module dma_arbiter(
                hclk,
                n_hreset,
                hgrant,
                hready,
                pready,
                apb_request,
                apb_backoff,
                ch0_ahb_req,
                ch0_apb_req,
                ch0_apb_grant,
                ch0_ahb_grant,
`ifdef one_channel
`else
                ch1_ahb_req,
                ch1_apb_req,
                ch1_apb_grant,
                ch1_ahb_grant,
`ifdef two_channel
`else
                ch2_ahb_req,
                ch2_apb_req,
                ch2_apb_grant,
                ch2_ahb_grant,
`ifdef three_channel
`else
                ch3_ahb_req,
                ch3_apb_req,
                ch3_apb_grant,
                ch3_ahb_grant,
`endif
`endif
`endif
                ahb_request,
                addr_drive,
                data_drive
                );

//=================
// Port assignments
//=================

  input         hclk;
  input         n_hreset;
  input         hgrant;
  input         hready;
  input         pready;
  output        apb_request;
  output        apb_backoff;
  input         ch0_ahb_req;
  input         ch0_apb_req;
  output        ch0_apb_grant;
  output        ch0_ahb_grant;
`ifdef one_channel
`else
  input         ch1_ahb_req;
  input         ch1_apb_req;
  output        ch1_apb_grant;
  output        ch1_ahb_grant;
`ifdef two_channel
`else
  input         ch2_ahb_req;
  input         ch2_apb_req;
  output        ch2_apb_grant;
  output        ch2_ahb_grant;
`ifdef three_channel
`else
  input         ch3_ahb_req;
  input         ch3_apb_req;
  output        ch3_apb_grant;
  output        ch3_ahb_grant;
`endif
`endif
`endif
  output        ahb_request;
  input         addr_drive;
  input         data_drive;

//===================
// Signal assignments
//===================

  wire          hclk;
  wire          n_hreset;
  wire          hgrant;
  wire          hready;
  wire          pready;
  reg           apb_request;

  wire          ch0_ahb_req;
  wire           ch0_ahb_grant;
  wire          ch0_apb_req;
  wire          ch0_apb_grant;
  reg     [5:0] ch0_count;

`ifdef one_channel
`else
  wire          ch1_ahb_req;
  wire          ch1_ahb_grant;
  wire          ch1_apb_req;
  wire          ch1_apb_grant;
  reg     [5:0] ch1_count;

`ifdef two_channel
`else
  wire          ch2_ahb_req;
  wire          ch2_ahb_grant;
  wire          ch2_apb_req;
  wire          ch2_apb_grant;
  reg     [5:0] ch2_count;

`ifdef three_channel
`else
  wire          ch3_ahb_req;
  wire          ch3_ahb_grant;
  wire          ch3_apb_req;
  wire          ch3_apb_grant;
  reg     [5:0] ch3_count;
`endif
`endif
`endif

  wire          addr_drive;
  wire          data_drive;

  reg           ahb_request;
  wire          apb_backoff;
  reg     [1:0] current_apb_state;
  reg     [1:0] next_apb_state;

  reg     [3:0] current_ahb_state;
  reg     [3:0] next_ahb_state;


//==========
// Main code
//==========

//======================
// APB arbitration logic
//======================

// Should APB arbitration take place in bridge or here?

// APB arbitration state machine

always @(ch0_apb_req or 
`ifdef one_channel
`else
        ch1_apb_req or  
`ifdef two_channel
`else
        ch2_apb_req or  
`ifdef three_channel
`else
        ch3_apb_req or 
`endif
`endif
`endif
        current_apb_state or apb_backoff)
begin
    next_apb_state = current_apb_state;
    case (current_apb_state)
        `ch0_apb :
            if (~ch0_apb_req | apb_backoff)
`ifdef one_channel
                next_apb_state = `ch0_apb;
`else
                next_apb_state = `ch1_apb;
        `ch1_apb :
            if (~ch1_apb_req | apb_backoff)
`ifdef two_channel
                next_apb_state = `ch0_apb;
`else
                next_apb_state = `ch2_apb;
        `ch2_apb :
            if (~ch2_apb_req | apb_backoff)
`ifdef three_channel
                next_apb_state = `ch0_apb;
`else
                next_apb_state = `ch3_apb;
        `ch3_apb :
            if (~ch3_apb_req | apb_backoff)
                next_apb_state = `ch0_apb;
`endif
`endif
`endif
        default :
            next_apb_state = `ch0_apb;
    endcase
end

// State control logic

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        current_apb_state <= `ch0_apb;
    else
        current_apb_state <= next_apb_state;
end

// apb grant logic
  assign ch0_apb_grant = ((current_apb_state == `ch0_apb) &
                            ch0_apb_req);
`ifdef one_channel
`else
  assign ch1_apb_grant = ((current_apb_state == `ch1_apb) &
                            ch1_apb_req);
`ifdef two_channel
`else
  assign ch2_apb_grant = ((current_apb_state == `ch2_apb) &
                            ch2_apb_req);
`ifdef three_channel
`else
  assign ch3_apb_grant = ((current_apb_state == `ch3_apb) &
                            ch3_apb_req);
`endif
`endif
`endif

// Generate apb request
// this signal is an or of the apb grant signals and is used in the bridge
// to pass control over to the dma
always @(
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
`ifdef one_channel
    apb_request = ch0_apb_grant; 
`else
    apb_request = ch0_apb_grant | 
`ifdef two_channel
                  ch1_apb_grant;
`else
                  ch1_apb_grant | 
`ifdef three_channel
                  ch2_apb_grant;
`else
                  ch2_apb_grant | 
                  ch3_apb_grant;
`endif
`endif
`endif
end

// APB backoff logic
// If a particular channel has been granted for > 64 clocks??? 
// Each grant needs to be monitored - if it is low clear the counter
// otherwise count, when count hits 63, apb_backoff asserted and grant dropped

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch0_count <= 6'b000000;
    else
    begin
        if (~ch0_apb_grant | pready)
            ch0_count <= 6'b000000;
        else
            ch0_count <= ch0_count + {5'b00000,ch0_apb_grant};
    end
end

`ifdef one_channel
`else
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch1_count <= 6'b000000;
    else
    begin
        if (~ch1_apb_grant | pready)
            ch1_count <= 6'b000000;
        else
            ch1_count <= ch1_count + {5'b00000,ch1_apb_grant};
    end
end

`ifdef two_channel
`else
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch2_count <= 6'b000000;
    else
    begin
        if (~ch2_apb_grant | pready)
            ch2_count <= 6'b000000;
        else
            ch2_count <= ch2_count + {5'b00000,ch2_apb_grant};
    end
end

`ifdef three_channel
`else
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch3_count <= 6'b000000;
    else
    begin
        if (~ch3_apb_grant | pready)
            ch3_count <= 6'b000000;
        else
            ch3_count <= ch3_count + {5'b00000,ch3_apb_grant};
    end
end
`endif
`endif
`endif

// count the number of backoffs in any 

// apb_backoff asserted if any of the counters reachs overflow
`ifdef one_channel
  assign apb_backoff = (&ch0_count); 
`else
  assign apb_backoff = (&ch0_count | 
`ifdef two_channel
                        &ch1_count);
`else
                        &ch1_count | 
`ifdef three_channel
                        &ch2_count); 
`else
                        &ch2_count | 
                        &ch3_count);
`endif
`endif
`endif

//======================
// AHB arbitration logic
//======================

// AHB arbitration state machine
// if the grant is removed from the dma the state must move to the next 
// check state even if the request line for the channel is still active
// this will retry on the next pass. if the data drive is asserted and the 
// addr drive is de-asserted the grant has been removed.
// Should back off be used on the AHB - need to ensure it would complete 
// cleanly if we allow it.

always @(ch0_ahb_req or 
`ifdef one_channel
`else
         ch1_ahb_req or 
`ifdef two_channel
`else
         ch2_ahb_req or 
`ifdef three_channel
`else
         ch3_ahb_req or 
`endif
`endif
`endif
         current_ahb_state or addr_drive or data_drive or hgrant or hready)
begin
    next_ahb_state = current_ahb_state;
    case (current_ahb_state)
        `ch0_check :
            if (ch0_ahb_req)
                next_ahb_state = `ch0_reqst;
            else
`ifdef one_channel
                next_ahb_state = `ch0_check;
        `ch0_reqst :
            if (hgrant)
                next_ahb_state = `ch0_grant;
            else if (~ch0_ahb_req)
                next_ahb_state = `ch0_check;
        `ch0_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch0_check;
`else
                 next_ahb_state = `ch1_check;
        `ch0_reqst :
            if (hgrant)
                next_ahb_state = `ch0_grant;
            else if (~ch0_ahb_req)
                next_ahb_state = `ch1_check;
        `ch0_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch1_check;
        `ch1_check :
            if (ch1_ahb_req)
                next_ahb_state = `ch1_reqst;
            else
`ifdef two_channel
                next_ahb_state = `ch0_check;
        `ch1_reqst :
            if (hgrant)
                next_ahb_state = `ch1_grant;
            else if (~ch1_ahb_req)
                next_ahb_state = `ch0_check;
        `ch1_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch0_check;
`else
                next_ahb_state = `ch2_check;
        `ch1_reqst :
            if (hgrant)
                next_ahb_state = `ch1_grant;
            else if (~ch1_ahb_req)
                next_ahb_state = `ch2_check;
        `ch1_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch2_check;
        `ch2_check :
            if (ch2_ahb_req)
                next_ahb_state = `ch2_reqst;
            else
`ifdef three_channel
                next_ahb_state = `ch0_check;
        `ch2_reqst :
            if (hgrant)
                next_ahb_state = `ch2_grant;
            else if (~ch2_ahb_req)
                next_ahb_state = `ch0_check;
        `ch2_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch0_check;
`else
                next_ahb_state = `ch3_check;
        `ch2_reqst :
            if (hgrant)
                next_ahb_state = `ch2_grant;
            else if (~ch2_ahb_req)
                next_ahb_state = `ch3_check;
        `ch2_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch3_check;
        `ch3_check :
            if (ch3_ahb_req)
                next_ahb_state = `ch3_reqst;
            else
                next_ahb_state = `ch0_check;
        `ch3_reqst :
            if (hgrant)
               // next_ahb_state = `ch2_grant;Debug Binata
                 next_ahb_state = `ch3_grant;
            else if (~ch3_ahb_req)
                next_ahb_state = `ch3_check;
        `ch3_grant :
            if (~hgrant & data_drive & hready & ~addr_drive)
                next_ahb_state = `ch0_check;
`endif
`endif
`endif
        default :
            next_ahb_state = `ch0_check;
    endcase
end

// Next state control

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        current_ahb_state <= `ch0_check;
    else
        current_ahb_state <= next_ahb_state;
end

// ahb_request output logic - used in clocked processes only.
// The requests from the channels needs to be reflected directly in the
// ahb_request output to ensure a single access will complete correctly.
// The channels will need to monitor the hgrant signal and if only
// a single access is being performed remove the request to ensure the grant
// is removed on the next cycle.  May need to use logical process rather than 
// clocked process if want to achieve single access!!!!!

always @(next_ahb_state or 
`ifdef one_channel
`else
         ch1_ahb_req or 
`ifdef two_channel
`else
         ch2_ahb_req or 
`ifdef three_channel
`else
         ch3_ahb_req or
`endif 
`endif 
`endif 
         ch0_ahb_req)
begin
`ifdef one_channel
    ahb_request = ((((next_ahb_state == `ch0_reqst) | 
                     (next_ahb_state == `ch0_grant)) & ch0_ahb_req));
`else
     ahb_request = ((((next_ahb_state == `ch0_reqst) | 
                     (next_ahb_state == `ch0_grant)) & ch0_ahb_req) |
`ifdef two_channel
                  (((next_ahb_state == `ch1_grant) | 
                    (next_ahb_state == `ch1_reqst)) & ch1_ahb_req));
`else
                  (((next_ahb_state == `ch1_grant) | 
                    (next_ahb_state == `ch1_reqst)) & ch1_ahb_req) |
`ifdef three_channel
                   (((next_ahb_state == `ch2_grant) | 
                     (next_ahb_state == `ch2_reqst)) & ch2_ahb_req));
`else
                   (((next_ahb_state == `ch2_grant) | 
                     (next_ahb_state == `ch2_reqst)) & ch2_ahb_req) |
                   (((next_ahb_state == `ch3_grant) | 
                     (next_ahb_state == `ch3_reqst)) & ch3_ahb_req));
`endif 
`endif 
`endif 
end

// channel grant logic
`ifdef RTL
    assign #0.1 ch0_ahb_grant = (next_ahb_state == `ch0_grant) & hgrant;

    `ifdef one_channel

    `else

      assign #0.1 ch1_ahb_grant = (next_ahb_state == `ch1_grant) & hgrant;

      `ifdef two_channel

      `else

         assign #0.1 ch2_ahb_grant = (next_ahb_state == `ch2_grant) & hgrant;

         `ifdef three_channel

         `else

           assign #0.1 ch3_ahb_grant = (next_ahb_state == `ch3_grant) & hgrant;

         `endif 

      `endif 

    `endif
`else
    assign ch0_ahb_grant = (next_ahb_state == `ch0_grant) & hgrant;

    `ifdef one_channel

    `else

      assign ch1_ahb_grant = (next_ahb_state == `ch1_grant) & hgrant;

      `ifdef two_channel

      `else
         assign ch2_ahb_grant = (next_ahb_state == `ch2_grant) & hgrant;

         `ifdef three_channel

         `else

           assign ch3_ahb_grant = (next_ahb_state == `ch3_grant) & hgrant;

         `endif 

      `endif 

    `endif

`endif
/*
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch0_ahb_grant <= 1'b0;
    else
        ch0_ahb_grant <= (next_ahb_state == `ch0_grant) | 
                         (next_ahb_state == `ch0_reqst);
end
                      
`ifdef one_channel
`else
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch1_ahb_grant <= 1'b0;
    else
        ch1_ahb_grant <= (next_ahb_state == `ch1_grant) | 
                         (next_ahb_state == `ch1_reqst);
end
                       
`ifdef two_channel
`else
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch2_ahb_grant <= 1'b0;
    else
        ch2_ahb_grant <= (next_ahb_state == `ch2_grant) | 
                         (next_ahb_state == `ch2_reqst);
end
                       
`ifdef three_channel
`else
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        ch3_ahb_grant <= 1'b0;
    else
        ch3_ahb_grant <= (next_ahb_state == `ch3_grant) | 
                         (next_ahb_state == `ch3_reqst);
end
`endif 
`endif 
`endif 
*/                        
endmodule
