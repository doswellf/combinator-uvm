//File name   : dma_ahb_config.v
//Title       : 
//Created     : 1999
//Description : DMA Channel configuration registers
//Notes       : The DMA config block will act as an AHB slave and will allow control
//              of the DMA config registers for each channel.  Once an access has
//              completed, successfully or otherwise the register is updated by 
//              a DMA access to the appropriate config register??????? 
//              (not sure about this may do it by direct modification.)
//Limitations : It is assumed that accesses to dma_config registers are
//              only word aligned - any other accesses will result in an 
//              error response. (could just do blind writes i.e result in bad
//              register contents)
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
//

//------------------------------------------------------------------------------
// Include Files
//------------------------------------------------------------------------------
`include   "dma_defs.v"             // DMA defines

//------------------------------------------------------------------------------
// Module Declaration
//------------------------------------------------------------------------------
// 
module dma_ahb_config(
            hclk,                       // ahb system clock
            n_hreset,                    // ahb system reset
            haddr,
            hsel,
            htrans,
            hwrite,
            hsize,
            hwdata,
            hready_in,
            // channel 0 registers
            dma_tadd_ch0,               // initial target address   (R/W)
            dma_sadd_ch0,               // initial source address   (R/W)
            dma_buff_ch0,               // buffer control           (R/W)
            dma_xfer_ch0,               // dma transfer reg         (RO/WO)
            dma_flow_ch0,               // flow control reg         (R/W)
            taddr_ch0,                  // current target address   (RO)
            saddr_ch0,                  // current source address   (RO)
            buff_pos_ch0,               // circular buffer position
            hready_out,
            hresp,
            hrdata,
            write_data,
            ahb_byte,
            ch0_taddr_sel,              // target address write sel
            ch0_saddr_sel,              // source address write sel
            ch0_buff_sel,               // buffer control write sel
            ch0_trans_sel,              // transfer control write sel
            ch0_flow_sel,               // flow control write sel
            ch0_abort_sel,              // abort ch0
            ch0_pos_sel,                // circular buffer position write sel
`ifdef one_channel
`else
            // channel 1 registers
            dma_tadd_ch1,        
            dma_sadd_ch1,        
            dma_buff_ch1,        
            dma_xfer_ch1,        
            dma_flow_ch1,        
            taddr_ch1,        
            saddr_ch1,        
            buff_pos_ch1,
            ch1_taddr_sel,
            ch1_saddr_sel,
            ch1_buff_sel,
            ch1_trans_sel,
            ch1_flow_sel,
            ch1_abort_sel,
            ch1_pos_sel,
`ifdef two_channel
`else
            // channel 2 registers
            dma_tadd_ch2,        
            dma_sadd_ch2,        
            dma_buff_ch2,        
            dma_xfer_ch2,        
            dma_flow_ch2,        
            taddr_ch2,        
            saddr_ch2,        
            buff_pos_ch2,
            ch2_taddr_sel,
            ch2_saddr_sel,
            ch2_buff_sel,
            ch2_trans_sel,
            ch2_flow_sel,
            ch2_abort_sel,
            ch2_pos_sel,
`ifdef three_channel
`else
            // channel 3 registers
            dma_tadd_ch3,        
            dma_sadd_ch3,        
            dma_buff_ch3,        
            dma_xfer_ch3,        
            dma_flow_ch3,        
            taddr_ch3,        
            saddr_ch3,        
            buff_pos_ch3,
            ch3_taddr_sel,
            ch3_saddr_sel,
            ch3_buff_sel,
            ch3_trans_sel,
            ch3_flow_sel,
            ch3_abort_sel,
            ch3_pos_sel,
`endif
`endif
`endif
            // interrupt control registers
            int_status,                 // Interrupt status register (RO)   
            int_mask,                   // interrupt mask register   (TRI)
            mask_en_sel,                // mask register set
            mask_dis_sel,               // mask register clear
            int_sel                     // status reg read
            );

//==================
// port declarations     
//==================

  input         hclk;
  input         n_hreset;
  input  [19:0] haddr;
  input         hsel;
  input   [1:0] htrans;
  input         hwrite;
  input   [2:0] hsize;
  input  [31:0] hwdata;
  input         hready_in;
  
  input  [31:0] dma_tadd_ch0;        
  input  [31:0] dma_sadd_ch0;        
  input  [31:0] dma_buff_ch0;        
  input  [31:0] dma_xfer_ch0;        
  input  [31:0] dma_flow_ch0;        
  input  [31:0] taddr_ch0;
  input  [31:0] saddr_ch0;
  input  [31:0] buff_pos_ch0;

  output        hready_out;
  output  [1:0] hresp;
  output [31:0] hrdata;
  output [31:0] write_data;
  output  [3:0] ahb_byte;

  output        ch0_taddr_sel;
  output        ch0_saddr_sel;
  output        ch0_buff_sel;
  output        ch0_trans_sel;
  output        ch0_flow_sel;
  output        ch0_abort_sel;
  output        ch0_pos_sel;

`ifdef one_channel
  input   [1:0] int_status;  
  input   [1:0] int_mask;    
`else
  input  [31:0] dma_tadd_ch1;        
  input  [31:0] dma_sadd_ch1;        
  input  [31:0] dma_buff_ch1;        
  input  [31:0] dma_xfer_ch1;        
  input  [31:0] dma_flow_ch1;        
  input  [31:0] taddr_ch1;
  input  [31:0] saddr_ch1;
  input  [31:0] buff_pos_ch1;

  output        ch1_taddr_sel;
  output        ch1_saddr_sel;
  output        ch1_buff_sel;
  output        ch1_trans_sel;
  output        ch1_flow_sel;
  output        ch1_abort_sel;
  output        ch1_pos_sel;

`ifdef two_channel
  input   [3:0] int_status;  
  input   [3:0] int_mask;    
`else
  input  [31:0] dma_tadd_ch2;        
  input  [31:0] dma_sadd_ch2;        
  input  [31:0] dma_buff_ch2;        
  input  [31:0] dma_xfer_ch2;        
  input  [31:0] dma_flow_ch2;        
  input  [31:0] taddr_ch2;
  input  [31:0] saddr_ch2;
  input  [31:0] buff_pos_ch2;

  output        ch2_taddr_sel;
  output        ch2_saddr_sel;
  output        ch2_buff_sel;
  output        ch2_trans_sel;
  output        ch2_flow_sel;
  output        ch2_abort_sel;
  output        ch2_pos_sel;

`ifdef three_channel
  input   [5:0] int_status;  
  input   [5:0] int_mask;    
`else
  input  [31:0] dma_tadd_ch3;        
  input  [31:0] dma_sadd_ch3;        
  input  [31:0] dma_buff_ch3;        
  input  [31:0] dma_xfer_ch3;        
  input  [31:0] dma_flow_ch3;        
  input  [31:0] taddr_ch3;
  input  [31:0] saddr_ch3;
  input  [31:0] buff_pos_ch3;

  output        ch3_taddr_sel;
  output        ch3_saddr_sel;
  output        ch3_buff_sel;
  output        ch3_trans_sel;
  output        ch3_flow_sel;
  output        ch3_abort_sel;
  output        ch3_pos_sel;

  input   [7:0] int_status;  
  input   [7:0] int_mask;    
`endif
`endif
`endif

  output        mask_en_sel; 
  output        mask_dis_sel;
  output        int_sel;      

//====================
// signal declarations
//====================

  wire          hclk;
  wire          n_hreset;
  wire   [19:0] haddr;
  wire          hsel;
  wire    [1:0] htrans;
  wire          hwrite;
  wire    [2:0] hsize;
  wire   [31:0] hwdata;
  wire          hready_in;

  reg           hready_out;
  reg     [1:0] hresp;
  reg    [31:0] hrdata;

  reg    [15:0] addr;
  reg     [1:0] size;
  reg           n_read;
  reg           access_valid;
  reg           valid;
  reg           mis_err;
  reg           r_hresp;
  reg           r_ready;
  reg    [31:0] read_data;
  reg    [31:0] write_data;

  wire   [31:0] dma_tadd_ch0;        
  wire   [31:0] dma_sadd_ch0;        
  wire   [31:0] dma_buff_ch0;        
  wire   [31:0] dma_xfer_ch0;        
  wire   [31:0] dma_flow_ch0;        
  wire   [31:0] taddr_ch0;
  wire   [31:0] saddr_ch0;
  wire   [31:0] buff_pos_ch0;

  reg           ch0_taddr_sel;
  reg           ch0_saddr_sel;
  reg           ch0_buff_sel;
  reg           ch0_trans_sel;
  reg           ch0_flow_sel;
  reg           ch0_abort_sel;
  reg           ch0_pos_sel;

`ifdef one_channel
  wire    [1:0] int_status;  
  wire    [1:0] int_mask;    
`else
  wire   [31:0] dma_tadd_ch1;        
  wire   [31:0] dma_sadd_ch1;        
  wire   [31:0] dma_buff_ch1;        
  wire   [31:0] dma_xfer_ch1;        
  wire   [31:0] dma_flow_ch1;        
  wire   [31:0] taddr_ch1;
  wire   [31:0] saddr_ch1;
  wire   [31:0] buff_pos_ch1;

  reg           ch1_taddr_sel;
  reg           ch1_saddr_sel;
  reg           ch1_buff_sel;
  reg           ch1_trans_sel;
  reg           ch1_flow_sel;
  reg           ch1_abort_sel;
  reg           ch1_pos_sel;

`ifdef two_channel
  wire    [3:0] int_status;  
  wire    [3:0] int_mask;    
`else
  wire   [31:0] dma_tadd_ch2;        
  wire   [31:0] dma_sadd_ch2;        
  wire   [31:0] dma_buff_ch2;        
  wire   [31:0] dma_xfer_ch2;        
  wire   [31:0] dma_flow_ch2;        
  wire   [31:0] taddr_ch2;
  wire   [31:0] saddr_ch2;
  wire   [31:0] buff_pos_ch2;

  reg           ch2_taddr_sel;
  reg           ch2_saddr_sel;
  reg           ch2_buff_sel;
  reg           ch2_trans_sel;
  reg           ch2_flow_sel;
  reg           ch2_abort_sel;
  reg           ch2_pos_sel;

`ifdef three_channel
  wire    [5:0] int_status;  
  wire    [5:0] int_mask;    
`else
  wire   [31:0] dma_tadd_ch3;        
  wire   [31:0] dma_sadd_ch3;        
  wire   [31:0] dma_buff_ch3;        
  wire   [31:0] dma_xfer_ch3;        
  wire   [31:0] dma_flow_ch3;        
  wire   [31:0] taddr_ch3;
  wire   [31:0] saddr_ch3;
  wire   [31:0] buff_pos_ch3;

  reg           ch3_taddr_sel;
  reg           ch3_saddr_sel;
  reg           ch3_buff_sel;
  reg           ch3_trans_sel;
  reg           ch3_flow_sel;
  reg           ch3_abort_sel;
  reg           ch3_pos_sel;

  wire    [7:0] int_status;  
  wire    [7:0] int_mask;    
`endif
`endif
`endif

  reg           mask_en_sel; 
  reg           mask_dis_sel;
  reg           int_sel;  
  reg     [3:0] ahb_byte;


//=====================
// main interface logic
//=====================

//------------------------------------------------------------------------------
// valid access control - ahb interface (ahb specific)
//------------------------------------------------------------------------------
// generates all ahb responses.
//------------------------------------------------------------------------------

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        addr <= 16'h0;
        size <= 2'b00;
        n_read <= 1'b0;
        access_valid <= 1'b0;
    end
    else
    begin 
        access_valid <= valid;
        if (hready_in & hsel)
        begin
            addr <= haddr[15:0];
            size <= hsize[1:0];
            n_read <= hwrite;
        end
    end
end

// detect a valid access
always @(hsel or hready_in or htrans or mis_err)
begin
   if (((htrans == `trn_nonseq) | (htrans == `trn_seq)) &
      hsel & hready_in & ~mis_err)
   begin
    //  valid <= 1'b1; commented by Binata
      valid = 1'b1; 
   end
   else
   begin
      //valid <= 1'b0; commented by Binata
      valid = 1'b0;
   end
end


// error detection logic
always @(haddr or hsize or htrans or hsel)
begin
  if (((haddr[0] & (hsize == {1'b0,`sz_half}))          |
      ((haddr[1:0] != 2'b00) & (hsize == {1'b0,`sz_word}))  |
       ((haddr[19:2] > 18'h23))) & 
      ((htrans == `trn_nonseq) | (htrans == `trn_seq)) & hsel )
    mis_err = 1'h1;
  else
    mis_err = 1'h0;
end 

// response
always @(posedge hclk or negedge n_hreset)
begin
  //added
  if (~n_hreset)
  begin
    hresp <= `rsp_okay;
    r_hresp <= 0;
  end
  else if ((htrans == `trn_idle) & hready_in)
  begin
    hresp <= `rsp_okay;
    r_hresp <= 0;
  end
  else if (mis_err)
  begin
    r_hresp <= 1;
    hresp <= `rsp_error;
  end
  else if (r_hresp == 1'b1)
  begin
    hresp <= `rsp_error;
    r_hresp <= 0;
  end
  else
  begin
    hresp <= `rsp_okay;
    r_hresp <= 0;
  end
end

// ahb ready signal
always @(posedge hclk or negedge n_hreset)
begin
  if (~n_hreset)
    r_ready <= 1'b1;
  else if ((((htrans == `trn_idle) | (htrans == `trn_busy)) & hsel &
             hready_in & ~mis_err) | r_hresp | ~hsel )
    r_ready <= 1'b1;
  else if (valid) 
          //assumes accesses will always complete with zero wait states
    r_ready <= 1'b1;
  else
    r_ready <= 1'b0;
end

// ahb ready signal
always @(r_ready)
begin
  hready_out = r_ready;
end


//read data
always @(read_data)
  hrdata = read_data;

//write data
always @(hwdata)
begin
    write_data = hwdata;
end

// generate byte select strobes to easily allow byte access
// Assume arm replicates data across the bus as necessary.
always @(size or addr) 
begin
    ahb_byte = 4'hf;
    if (size == `sz_byte)
    begin
        if (addr[1:0] == 2'b00)
            ahb_byte = 4'b0001;
        else if (addr[1:0] == 2'b01)
            ahb_byte = 4'b0010;
        else if (addr[1:0] == 2'b10)
            ahb_byte = 4'b0100;
        else
            ahb_byte = 4'b1000;
    end
    else if (size == `sz_half)
    begin
        if (addr[1] == 1'b0)
            ahb_byte = 4'b0011;
        else
            ahb_byte = 4'b1100;
    end
    else
        ahb_byte = 4'b1111;
end

//==========
// registers
//==========

//==============
// write process
//==============
// generate write strobes for each register - this enables the registers
// to be located in the relevant blocks and updated as necessary

//==============
// CH0 registers
//==============

always @(n_read or access_valid or addr or write_data or ahb_byte)
begin
    ch0_taddr_sel = 1'b0;
    ch0_saddr_sel = 1'b0;
    ch0_buff_sel = 1'b0;
    ch0_trans_sel = 1'b0;
    ch0_flow_sel = 1'b0;
    ch0_abort_sel = 1'b0;
    ch0_pos_sel = 1'b0;
    if (n_read & access_valid)
        case ({addr[15:2], 2'b00})
            `ch0_taddr :
                ch0_taddr_sel = 1'b1;
            `ch0_saddr :
                ch0_saddr_sel = 1'b1;
            `ch0_buff :
                ch0_buff_sel = 1'b1;
            `ch0_trans :
            begin
                ch0_trans_sel = 1'b1;
                if (write_data[17] & ahb_byte[2])
                    ch0_abort_sel = 1'b1;
            end
            `ch0_flow :
                ch0_flow_sel = 1'b1;
            `ch0_pbuff :
                ch0_pos_sel = 1'b1;
            default:
            begin
                ch0_taddr_sel = 1'b0;
                ch0_saddr_sel = 1'b0;
                ch0_buff_sel = 1'b0;
                ch0_trans_sel = 1'b0;
                ch0_flow_sel = 1'b0;
                ch0_abort_sel = 1'b0;
                ch0_pos_sel = 1'b0;
            end
        endcase
end

`ifdef one_channel
`else
//==============
// ch1 registers
//==============

always @(n_read or access_valid or addr or write_data or ahb_byte)
begin
    ch1_taddr_sel = 1'b0;
    ch1_saddr_sel = 1'b0;
    ch1_buff_sel = 1'b0;
    ch1_trans_sel = 1'b0;
    ch1_flow_sel = 1'b0;
    ch1_abort_sel = 1'b0;
    ch1_pos_sel = 1'b0;
    if (n_read & access_valid)
        case ({addr[15:2], 2'b00})
            `ch1_taddr :
                ch1_taddr_sel = 1'b1;
            `ch1_saddr :
                ch1_saddr_sel = 1'b1;
            `ch1_buff :
                ch1_buff_sel = 1'b1;
            `ch1_trans :
            begin
                ch1_trans_sel = 1'b1;
                if (write_data[17] & ahb_byte[2])
                    ch1_abort_sel = 1'b1;
            end
            `ch1_flow :
                ch1_flow_sel = 1'b1;
            `ch1_pbuff :
                ch1_pos_sel = 1'b1;
            default
            begin
                ch1_taddr_sel = 1'b0;
                ch1_saddr_sel = 1'b0;
                ch1_buff_sel = 1'b0;
                ch1_trans_sel = 1'b0;
                ch1_flow_sel = 1'b0;
                ch1_abort_sel = 1'b0;
                ch1_pos_sel = 1'b0;
            end
        endcase
end

`ifdef two_channel
`else
//==============
// ch2 registers
//==============

always @(n_read or access_valid or addr or write_data or ahb_byte)
begin
    ch2_taddr_sel = 1'b0;
    ch2_saddr_sel = 1'b0;
    ch2_buff_sel = 1'b0;
    ch2_trans_sel = 1'b0;
    ch2_flow_sel = 1'b0;
    ch2_abort_sel = 1'b0;
    ch2_pos_sel = 1'b0;
    if (n_read & access_valid)
        case ({addr[15:2], 2'b00})
            `ch2_taddr :
                ch2_taddr_sel = 1'b1;
            `ch2_saddr :
                ch2_saddr_sel = 1'b1;
            `ch2_buff :
                ch2_buff_sel = 1'b1;
            `ch2_trans :
            begin
                ch2_trans_sel = 1'b1;
                if (write_data[17] & ahb_byte[2])
                    ch2_abort_sel = 1'b1;
            end
            `ch2_flow :
                ch2_flow_sel = 1'b1;
            `ch2_pbuff :
                ch2_pos_sel = 1'b1;
            default
            begin
                ch2_taddr_sel = 1'b0;
                ch2_saddr_sel = 1'b0;
                ch2_buff_sel = 1'b0;
                ch2_trans_sel = 1'b0;
                ch2_flow_sel = 1'b0;
                ch2_abort_sel = 1'b0;
                ch2_pos_sel = 1'b0;
            end
        endcase
end

`ifdef three_channel
`else
//==============
// ch3 registers
//==============

always @(n_read or access_valid or addr or write_data or ahb_byte)
begin
    ch3_taddr_sel = 1'b0;
    ch3_saddr_sel = 1'b0;
    ch3_buff_sel = 1'b0;
    ch3_trans_sel = 1'b0;
    ch3_flow_sel = 1'b0;
    ch3_abort_sel = 1'b0;
    ch3_pos_sel = 1'b0;
    if (n_read & access_valid)
        case ({addr[15:2], 2'b00})
            `ch3_taddr :
                ch3_taddr_sel = 1'b1;
            `ch3_saddr :
                ch3_saddr_sel = 1'b1;
            `ch3_buff :
                ch3_buff_sel = 1'b1;
            `ch3_trans :
            begin
                ch3_trans_sel = 1'b1;
                if (write_data[17] & ahb_byte[2])
                    ch3_abort_sel = 1'b1;
            end
            `ch3_flow :
                ch3_flow_sel = 1'b1;
            `ch3_pbuff :
                ch3_pos_sel = 1'b1;
            default
            begin
                ch3_taddr_sel = 1'b0;
                ch3_saddr_sel = 1'b0;
                ch3_buff_sel = 1'b0;
                ch3_trans_sel = 1'b0;
                ch3_flow_sel = 1'b0;
                ch3_abort_sel = 1'b0;
                ch3_pos_sel = 1'b0;
            end
        endcase
end
`endif
`endif
`endif

// Interrupt control registers
always @(n_read or access_valid or addr)
begin
    mask_en_sel = 1'b0;
    mask_dis_sel = 1'b0;
    int_sel = 1'b0;
    if (n_read & access_valid)
        case ({addr[15:2], 2'b00})
        `int_mask_en :
            mask_en_sel = 1'b1;
        `int_mask_dis :
            mask_dis_sel = 1'b1;
        `int_status :
            int_sel = 1'b1;
        default :
        begin
            mask_en_sel = 1'b0;
            mask_dis_sel = 1'b0;
            int_sel = 1'b0;
        end
        endcase
end

//=============
// read process
//=============

//always @(addr or access_valid or size or n_read or by Binata
always @(addr or access_valid  or n_read or
        dma_tadd_ch0 or dma_sadd_ch0 or dma_buff_ch0 or dma_xfer_ch0 or 
        dma_flow_ch0 or saddr_ch0 or taddr_ch0 or buff_pos_ch0 or
`ifdef one_channel
`else
        dma_tadd_ch1 or dma_sadd_ch1 or dma_buff_ch1 or dma_xfer_ch1 or 
        dma_flow_ch1 or saddr_ch1 or taddr_ch1 or buff_pos_ch1 or
`ifdef two_channel
`else
        dma_tadd_ch2 or dma_sadd_ch2 or dma_buff_ch2 or dma_xfer_ch2 or 
        dma_flow_ch2 or saddr_ch2 or taddr_ch2 or buff_pos_ch2 or
`ifdef three_channel
`else
        dma_tadd_ch3 or dma_sadd_ch3 or dma_buff_ch3 or dma_xfer_ch3 or 
        dma_flow_ch3 or saddr_ch3 or taddr_ch3 or buff_pos_ch3 or
`endif
`endif
`endif
        int_status or int_mask)
begin
    read_data = 32'h00000000;
    if (access_valid & ~n_read)
    begin
        case ({addr[15:2], 2'b00})
            `ch0_taddr :
                read_data = dma_tadd_ch0;
            `ch0_saddr :
                read_data = dma_sadd_ch0;
            `ch0_buff  :
                read_data = dma_buff_ch0;
            `ch0_trans :
                read_data = dma_xfer_ch0;
            `ch0_flow :
                read_data = dma_flow_ch0;
            `ch0_ctadd :
                read_data = taddr_ch0;
            `ch0_csadd :
                read_data = saddr_ch0;
            `ch0_pbuff :
                read_data = buff_pos_ch0;
`ifdef one_channel
            `int_status :
            begin
                read_data[1:0] = int_status;
            end
            `int_mask :
                read_data[1:0] = int_mask;
`else
            `ch1_taddr :
                read_data = dma_tadd_ch1;
            `ch1_saddr :
                read_data = dma_sadd_ch1;
            `ch1_buff  :
                read_data = dma_buff_ch1;
            `ch1_trans :
                read_data = dma_xfer_ch1;
            `ch1_flow :
                read_data = dma_flow_ch1;
            `ch1_ctadd :
                read_data = taddr_ch1;
            `ch1_csadd :
                read_data = saddr_ch1;
            `ch1_pbuff :
                read_data = buff_pos_ch1;
`ifdef two_channel
            `int_status :
            begin
                read_data[3:0] = int_status;
            end
            `int_mask :
                read_data[3:0] = int_mask;
`else
            `ch2_taddr :
                read_data = dma_tadd_ch2;
            `ch2_saddr :
                read_data = dma_sadd_ch2;
            `ch2_buff  :
                read_data = dma_buff_ch2;
            `ch2_trans :
                read_data = dma_xfer_ch2;
            `ch2_flow :
                read_data = dma_flow_ch2;
            `ch2_ctadd :
                read_data = taddr_ch2;
            `ch2_csadd :
                read_data = saddr_ch2;
            `ch2_pbuff :
                read_data = buff_pos_ch2;
`ifdef three_channel
            `int_status :
            begin
                read_data[5:0] = int_status;
            end
            `int_mask :
                read_data[5:0] = int_mask;
`else
            `ch3_taddr :
                read_data = dma_tadd_ch3;
            `ch3_saddr :
                read_data = dma_sadd_ch3;
            `ch3_buff  :
                read_data = dma_buff_ch3;
            `ch3_trans :
                read_data = dma_xfer_ch3;
            `ch3_flow :
                read_data = dma_flow_ch3;
            `ch3_ctadd :
                read_data = taddr_ch3;
            `ch3_csadd :
                read_data = saddr_ch3;
            `ch3_pbuff :
                read_data = buff_pos_ch3;
            `int_status :
            begin
                read_data[7:0] = int_status;
            end
            `int_mask :
                read_data[7:0] = int_mask;
`endif
`endif
`endif
            default :
            begin
                read_data = 32'h00000000;
            end
        endcase
    end
end

endmodule
