//File name   : dma_channel.v
//Title       : 
//Created     : 1999
//Description : DMA Channel
//Notes       : The DMA channel control the accesses performed over both the apb 
//	        and ahb largest module in the dma.
//
//Limitations : Need to think about accesses being cut short - time outs etc..
//              Not correctly wroked out how to deal with circular buffers yet!
//              
//Assumptions :
//          1. Transfers to apb space will ignore bit 1 of the address as no
//              data will exist in the upper half of each word address i.e
//              this will effectively repeat the lower half word.  Should
//              limit software to only provide address with either 00 or 01 
//		offset
//          2. Slot available indicates four bytes can be written
//
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
module dma_channel(
        hclk,
        n_hreset,
// config registers
        write_data,
        ahb_byte,
        dma_tadd,
        dma_sadd,
        dma_buff,
        dma_xfer,
        taddr,
        saddr,
        buff_pos,
        taddr_sel,
        saddr_sel,
        buff_sel,
        trans_sel,
        abort_sel,
        pos_sel,
// signals to/from arbiter
        ahb_req,
        apb_req,
        ahb_grant,
        apb_grant,
// signals to ahb mux
        haddr,
        htrans,
        hwrite,
        hsize,
        hburst,
        hprot,
        hwdata,
// signals from ahb mux
        hready,
        hresp,
        hrdata,
// signals to apb mux
        //pclk, commented by Binata
        //presetn,commented by Binata
        paddr,
        pwrite,
        pwdata,
        penable,
        byte_access,
// signals from apb mux
        pready,
        prdata,
        apb_backoff,
// flow control inputs
        data_available,         // byte available
        slot_available,         // space available
        word_available,         // word (4 bytes) available
        double_clk,
// status outputs
        complete,
        abort
        );

//==================
// Port declarations
//==================

  input         hclk;
  input         n_hreset;
// config registers
  input  [31:0] write_data;
  input   [3:0] ahb_byte;
  output [31:0] dma_tadd;
  output [31:0] dma_sadd;
  output [31:0] dma_buff;
  output [31:0] dma_xfer;
  output [31:0] taddr;
  output [31:0] saddr;
  output [31:0] buff_pos;
  input         taddr_sel;
  input         saddr_sel;
  input         buff_sel;
  input         trans_sel;
  input         abort_sel;
  input         pos_sel;
// signals to/from arbiter
  output        ahb_req;
  output        apb_req;
  input         ahb_grant;
  input         apb_grant;
// signals to ahb mux
  output [31:0] haddr;
  output  [1:0] htrans;
  output        hwrite;
  output  [2:0] hsize;
  output  [2:0] hburst;
  output  [3:0] hprot;
  output [31:0] hwdata;
// signals from ahb mux
  input         hready;
  input   [1:0] hresp;
  input  [31:0] hrdata;
// signals to apb mux
  //input         pclk;commented Binata
  //input         presetn;
  output [19:0] paddr;
  output        pwrite;
  output [15:0] pwdata;
  output        penable;
  output        byte_access;
// signals from apb mux
  input         pready;
  input  [15:0] prdata;
  input         apb_backoff;
// flow control inputs
  input         data_available;
  input         slot_available;
  input         word_available;
  input         double_clk;
// status outputs
  output        complete;
  output        abort;

//====================
// Signal declarations
//====================

  wire          hclk;
  wire          n_hreset;
// config registers
  wire   [31:0] write_data;
  wire    [3:0] ahb_byte;
  reg    [31:0] dma_tadd;
  reg    [31:0] dma_sadd;
  reg    [31:0] dma_buff;
  reg    [31:0] dma_xfer;
  wire   [31:0] buff_pos;
  wire          taddr_sel;
  wire          saddr_sel;
  wire          buff_sel;
  wire          trans_sel;
  wire          abort_sel;
  wire          pos_sel;
// Dynamic config register values
  reg    [15:0] xfer_size;
  reg           xfer_start;
`ifdef circular
  reg    [13:0] tsize;
  reg    [13:0] ssize;
  reg    [13:0] tpos;
  reg    [13:0] spos;
`endif
  reg           tcirc_buff;
  reg           scirc_buff;
  reg           tnoinc_buff;
  reg           snoinc_buff;
  reg    [31:0] saddr;
  reg    [31:0] taddr;
// signals to/from arbiter
//  reg           ahb_req;            // Set when an access is required
  wire          ahb_req;            // Set when an access is required
  reg           apb_req;
  reg           apb_req_next;
  wire          ahb_grant;          // Set when an access has been granted
  wire          apb_grant;
// signals to ahb mux
  reg    [31:0] haddr;
  reg     [1:0] htrans;
  reg           hwrite;
  reg     [2:0] hsize;
  wire    [2:0] hburst;
  wire    [3:0] hprot;
  reg    [31:0] hwdata;
// signals from ahb mux
  wire          hready;
  wire    [1:0] hresp;
  wire   [31:0] hrdata;
// signals to apb mux
  //wire          pclk;
  //wire          presetn;
  reg    [19:0] paddr;
  reg           pwrite;
  reg    [15:0] pwdata;
  reg           penable;
  reg           byte_access_next;
  reg           byte_access_last;
  reg           byte_access;
// signals from apb mux
  wire          pready;
  wire   [15:0] prdata;
  wire          apb_backoff;
// flow control wires
  wire          data_available;
  wire          slot_available;
  wire          word_available;
  wire          double_clk;
// status outputs
  reg           complete;
  reg           complete_next;
  reg           abort;              // used to finish current transfer and end

// DMA internal control signals
  reg           end_xfer;           // set when xfer_size is decremented to zero
  wire   [31:0] APB_base;           // sets apb space COMMENTED Binata
`ifdef DMA_APB
  reg           source_apb;         // set if source address is within apb space
  reg           target_apb;         // set if target address is within apb space
`else 
  wire          source_apb;         // set 0
  wire          target_apb;         // set 0
`endif 
  reg           write_grant;        // read to write handover control
  reg           write_complete;     // write to read handover control

  //reg     [7:0] data_reg[0:10];     // register bank used to store burst read 
  reg     [7:0] data_reg[10:0];     // register bank used to store burst read 
                                    // data and to control residue etc.
                                    // TOP THREE POSITIONS ARE ALWAYS TIED LOW
  reg     [1:0] read_pntr;          // read pointer into reg bank (for ahb reads)
  reg     [2:0] write_pntr;         // write pointer

  reg           first_read;         // Used to identify first read
  wire    [4:0] dma_read_state;     // Read state control
  wire    [4:0] next_read_state;    // next read state 
  wire    [4:0] dma_write_state;    // Write state control
  wire    [4:0] next_write_state;   // next write state

  reg     [3:0] data_count;         // Counts number of valid bytes in buffer
  reg           continue_read; 
  reg           continue_write;

  //integer i;                        // used in for loop to clear data_reg bank
  integer count;                        // used in for loop to clear data_reg bank

// APB specific signals
  reg           less_word;          // asserted when less then four bytes remain
  reg           less_dble;          // asserted when less then eight bytes remain
  reg    [29:0] stemp;              // used to calculate saddr + 4
  reg    [29:0] ttemp;              // used to calculate taddr + 4
`ifdef circular
  reg    [13:0] scirc_temp;         // used to simplify logic to the eye
  reg    [13:0] tcirc_temp;         // used to simplify logic to the eye
`endif
  reg     [1:0] write_count;        // counts number of apb bytes written
  reg     [7:0] temp_data0;         // used in apb reads
  reg     [7:0] temp_data1;         // used in apb reads
  reg     [7:0] temp_data2;         // used in apb reads
  reg     [7:0] temp_data3;         // used in apb reads
  reg           count_two;          // counts two cycles when double_clk
  reg           paddr_mux;          
// register mux select to prevent glitch on paddr
  reg           iahb_req;           // internal ahb_req (avoids glitches)
  reg     [2:0] backoff_count;      
// safety signal to abort if repeated backoffs occur
  reg           apb_buf_full;       // reg to prevent over read on apb

wire [7:0] hold_fifo_0;
wire [7:0] hold_fifo_1;
wire [7:0] hold_fifo_2;
wire [7:0] hold_fifo_3;
wire [7:0] hold_fifo_4;
wire [7:0] hold_fifo_5;
wire [7:0] hold_fifo_6;
wire [7:0] hold_fifo_7;
wire [7:0] hold_fifo_8;
wire [7:0] hold_fifo_9;
wire [7:0] hold_fifo_10;

assign hold_fifo_0  = data_reg[0];
assign hold_fifo_1  = data_reg[1];
assign hold_fifo_2  = data_reg[2];
assign hold_fifo_3  = data_reg[3];
assign hold_fifo_4  = data_reg[4];
assign hold_fifo_5  = data_reg[5];
assign hold_fifo_6  = data_reg[6];
assign hold_fifo_7  = data_reg[7];
assign hold_fifo_8  = data_reg[8];
assign hold_fifo_9  = data_reg[9];
assign hold_fifo_10 = data_reg[10];


//==========
// Main code
//==========

// Config registers control - these registers can be written using the byte
// write strobes.  For reads the register values are output.  If a write occurs
// to one of the registers before an access has completed an abort is issued.
// The write data is rotated to ensure the correct data is presented.

// Need to add logic to enable automatic updates of the registers

// transfer control register - The xfer size is updated when the write
// state machine performs each write successfully, the amount by which 
// it decrements is controlled by the write control logic:
// next_size can be set to either 1, 2 or 4.
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        xfer_size <= 16'h0000;
        xfer_start <= 1'b0;
    end
    else
    begin
        if ((dma_write_state == `write_ahb_staddr)      |
            (dma_write_state == `write_ahb_addr)) 
        begin
            if (hready)
                if (hsize == `sz_byte)
                    //xfer_size <= xfer_size - 1;
                    xfer_size <= xfer_size - 16'h0001;
                else if (hsize == `sz_half)
                    xfer_size <= xfer_size - 16'h0002;
                else if (hsize == `sz_word)
                    xfer_size <= xfer_size - 16'h0004;
        end
        //  The size is decremented by either 2 or 4 depending on byte_access
        else if (((dma_write_state == `write_apb_main) & pready & 
                 (~double_clk | count_two))) 
        begin
            if (byte_access)
                xfer_size <= xfer_size - 16'h0001;
            else
                xfer_size <= xfer_size - 16'h0002;
        end
      
        else
        begin
            if (trans_sel & ~xfer_start)
            begin
                if (ahb_byte[0])
                xfer_size[7:0] <= write_data[7:0];
                if (ahb_byte[1])
                xfer_size[15:8] <= write_data[15:8];
                if (ahb_byte[2])
                xfer_start <= write_data[16];
            end
        end
        if (end_xfer | abort)
            xfer_start <= 1'b0;
    end
end 

always @(xfer_size or xfer_start or abort)
begin
    dma_xfer = {14'h0000, abort, xfer_start, xfer_size};
end

// buffer control register
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
`ifdef circular
        tsize <= 14'h0000;
        ssize <= 14'h0000;
`endif
        tcirc_buff <= 1'b0;
        scirc_buff <= 1'b0;
        tnoinc_buff <= 1'b0;
        snoinc_buff <= 1'b0;
    end
    else
    begin
        if (buff_sel & ~xfer_start)
        begin
`ifdef circular
            if (ahb_byte[0])
                tsize[7:0]  <= write_data[7:0];
            if (ahb_byte[1])
            begin
                tsize[13:8] <= write_data[13:8];
                tcirc_buff  <= write_data[14];
            end
            if (ahb_byte[2])
            begin
                ssize       <= write_data[23:16];
            end
            if (ahb_byte[3])
            begin
                ssize       <= write_data[29:24];
                scirc_buff  <= write_data[30];
            end
`else
            tcirc_buff  <= 1'b0;
            scirc_buff  <= 1'b0;
`endif
            if (ahb_byte[1])
                tnoinc_buff <= write_data[15];
            if (ahb_byte[3])
                snoinc_buff <= write_data[31];
        end
    end
end 

always @(tcirc_buff or tnoinc_buff or 
`ifdef circular
            tsize or ssize or 
`endif
            scirc_buff or snoinc_buff)
begin
`ifdef circular
    dma_buff = {snoinc_buff, scirc_buff, ssize, 
                tnoinc_buff, tcirc_buff, tsize};
`else
    dma_buff = {snoinc_buff, scirc_buff, 14'h0000, 
                tnoinc_buff, tcirc_buff, 14'h0000};
`endif
end

// source address register
// the source address is updated after each read depending on the state of 
// the buffer register - should be able to use the next_size to control
// the size of the increment.  With circular buffers the size is in bytes
// this has the implication that at the top of the buffer accesses may need 
// to be broken across the boundary, therefore a separate signal is required 
// to control this boundary.  This can be similar to the xfer_size being 
// reduced each access by the required amount and if this results in a 
// value less than 4 this access is broken into smaller chunks.
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        dma_sadd <= 32'h00000000;
        saddr <= 32'h00000000;
        stemp <= 30'h00000000;
`ifdef circular
        spos <= 14'h0000;
        scirc_temp <= 14'h0000;
`endif
    end
    else
    begin
        // Increment the address after each is accepted
        // Assume circular buffers and no-inc buffers do not exist on
        // ahb therefore can use dma_sadd to store data
        //stemp = saddr[31:2] + 1;
        stemp <= saddr[31:2] + 30'h00000001;
`ifdef circular
        scirc_temp <= ssize[13:0] - 1;
`endif
        if (((dma_read_state == `read_ahb_addr))    &
            hready)
        begin
                dma_sadd <= saddr;
                saddr <= {stemp, 2'b00};
        end
        // APB accesses require the address to be updated after each access 
        // unless the access is to a non-incrementing buffer.  The byte_access
        // signal can be used to increment by either 1 or 2.  It is important
        // to remember that each location is on a word boundary but only the
        // bottom two bytes are valid therefore address would increment as
        // 0000, 0001, 0100, 0101, 1000, 1001, 1100, 1101
        else if (~snoinc_buff & ((dma_read_state == `read_apb_data) & 
                 (~double_clk | count_two)))
`ifdef circular
        begin
            if ((spos == scirc_temp) & scirc_buff)
            begin
                saddr <= dma_sadd;
                spos <= 14'h0000;
            end
            else
`endif
            begin
                if (&(saddr[1:0]) | (~byte_access & saddr[1]))
                    saddr <= {stemp, 2'b00};
                else if (~byte_access | saddr[0])
                    saddr[1:0] <= 2'b10;
                else
                    saddr[0] <= ~saddr[0];   
                // can assume increase of one as byte access is forced high in
                // circular buffer mode
`ifdef circular
                if (scirc_buff)
                    spos <= spos + 1;                
            end
`endif
        end
        // at the end of an access if the source was an ahb update the address
        // to point to the next byte not used
        else if (dma_read_state == `xfer_finish)
        begin
            if (~source_apb)
            begin
                if (|write_pntr[1:0])
                begin
                    dma_sadd <= {dma_sadd[31:2], write_pntr[1:0]};
                    saddr <= {dma_sadd[31:2], write_pntr[1:0]};
                end
                else
                begin
                    dma_sadd <= saddr;
                end                   
            end
        end
        else
        begin
            if (saddr_sel & ~xfer_start)
            begin
                if (ahb_byte[0])
                begin
                    dma_sadd[7:0]   <= write_data[7:0];
                    saddr[7:0]      <= write_data[7:0];
                end
                if (ahb_byte[1])
                begin
                    dma_sadd[15:8]  <= write_data[15:8];
                    saddr[15:8]     <= write_data[15:8];
                end
                if (ahb_byte[2])
                begin
                    dma_sadd[23:16] <= write_data[23:16];
                    saddr[23:16]    <= write_data[23:16];
                end
                if (ahb_byte[3])
                begin
                    dma_sadd[31:24] <= write_data[31:24];
                    saddr[31:24]    <= write_data[31:24];
                end
            end
`ifdef circular
            else if (pos_sel & ~xfer_start)
            begin
                if (ahb_byte[2])
                    spos <= write_data[23:16];
                if (ahb_byte[3])
                    spos <= write_data[29:24]; 
            end
`endif
        end
    end
end 

// target address register
// need to update after each successful read depending upon buffer settings
// and using the next_size value to control the address increment
// Need to update the address ready for the next access therefore on writes
// the first address is output in write_ahb_addr, if a burst is occuring 
// the next address will occur when we move into addr_data state.
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        dma_tadd <= 32'h00000000;
        taddr <= 32'h00000000;
        ttemp <= 30'h00000000;
`ifdef circular
        tpos <= 14'h0000;
        tcirc_temp <= 14'h0000;
`endif
    end
    else
    begin
        // Assume only standard accesses on ahb!
        ttemp <= taddr[31:2] + 30'h00000001;
`ifdef circular
        //tcirc_temp = tsize[13:0] - 1;
        tcirc_temp <= tsize[13:0] - 1;
`endif
        if (((dma_write_state == `write_ahb_staddr)      |
             (dma_write_state == `write_ahb_addr))  &
            hready)
        begin
            if (hsize == `sz_byte)
                taddr <= taddr + 1;
            else if (hsize == `sz_half)
                taddr <= taddr + 2;
            else if (hsize == `sz_word)
                taddr <= taddr + 4;
        end
        // APB accesses require the address to be updated after each access 
        // unless the access is to a non-incrementing buffer.  The byte_access
        // signal can be used to increment by either 1 or 2.
        else if (~tnoinc_buff & ((dma_write_state == `write_apb_data) &
                 (~double_clk | count_two)))
`ifdef circular
        begin
            if ((tpos == tcirc_temp) & tcirc_buff)
            begin
                taddr <= dma_tadd;
                tpos <= 14'h0000;
            end
            else
`endif
            begin
                if (&(taddr[1:0]) | (~byte_access & taddr[1]))
                    taddr <= {ttemp, 2'b00};
                else if (~byte_access | taddr[0])
                    taddr[1:0] <= 2'b10;
                else
                    taddr[0] <= ~taddr[0];                    
`ifdef circular
                if (tcirc_buff)
                    tpos <= tpos + 1;
            end
`endif
        end
        else
        begin
            if (taddr_sel & ~xfer_start)
            begin
                if (ahb_byte[0])
                begin
                    dma_tadd[7:0]   <= write_data[7:0];
                    taddr[7:0]      <= write_data[7:0];
                end
                if (ahb_byte[1])
                begin
                    dma_tadd[15:8]  <= write_data[15:8];
                    taddr[15:8]     <= write_data[15:8];
                end
                if (ahb_byte[2])
                begin
                    dma_tadd[23:16] <= write_data[23:16];
                    taddr[23:16]    <= write_data[23:16];
                end
                if (ahb_byte[3])
                begin
                    dma_tadd[31:24] <= write_data[31:24];
                    taddr[31:24]    <= write_data[31:24];
                end
            end
`ifdef circular
            else if (pos_sel & ~xfer_start)
            begin
                if (ahb_byte[0])
                    tpos <= write_data[7:0];
                if (ahb_byte[1])
                    tpos <= write_data[13:8];
            end
`endif
        end
    end
end 

// need to construct buff poss register

`ifdef circular
  assign buff_pos = {2'b0, spos, 2'b0, tpos};
`else
  assign buff_pos = 32'h00000000;
`endif

// if abort register is written or any of the control registers are written -
// except flow control - and the transfer has started assert the abort.
// this will cause the current transfer to complete and move to the stop
// state where an abort interrupt is raised instead of a  complete interrupt.
// The target and source addresses should be updated to reflect the last 
// successful transfer.
// If an AHB transfer returns any response except okay the transfer should be
// aborted.

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        abort <= 1'b0;
    else
    begin
        if (abort_sel)
            abort <= 1'b1;
        else if ((taddr_sel | saddr_sel | buff_sel | trans_sel | abort_sel) &
                 xfer_start)
            abort <= 1'b1;
        else if (backoff_count == 3'b111)
            abort <= 1'b1;
        else if (((dma_read_state == `read_ahb_data) |
                  (dma_write_state == `write_ahb_data) |
                  (dma_write_state == `write_ahb_stdata)) & 
                  hready & (hresp != `rsp_okay))
            abort <= 1'b1;
        else if (~xfer_start & (dma_read_state == `idle)
                             & (dma_write_state == `idle))
            abort <= 1'b0;
    end
end
        
// backoff_count - each time backoff is asserted for this channel on 
// a particular transfer increment this counter, if it reachs 7 
// generate a channel abort
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        backoff_count <= 3'b000;
    else
    begin
        if (apb_backoff & xfer_start & apb_grant)
            backoff_count <= backoff_count + 3'b001;
        else if (pready | ~xfer_start)
            backoff_count <= 3'b000;            
    end
end

// generate status outputs
// the complete flag is the xfer_finish state and the abort flag is ?
always @(next_read_state)
begin
    complete_next = (next_read_state == `xfer_finish);
end

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        complete <= 1'b0;
    else
        complete <= complete_next;
end
//===========================
// Main channel control code.
//===========================

//-------------------------
// Generate control signals
//-------------------------

`ifdef DMA_APB
// REMOVE UNTIL APB SECTION ADDED
//assign APB_base   = `dma_APB_base;

// Decode source and target addresses to decode if either are within apb space
always @(taddr or saddr or APB_base)
begin
    if (taddr[`dma_apb_upper_bit:`dma_apb_lower_bit] == APB_base[`dma_apb_upper_bit:
    `dma_apb_lower_bit])
        target_apb = 1'b1;
    else 
        target_apb = 1'b0;

    if (saddr[`dma_apb_upper_bit:`dma_apb_lower_bit] == APB_base[`dma_apb_upper_bit:
    `dma_apb_lower_bit])
        source_apb = 1'b1;
    else 
        source_apb = 1'b0;
end
`else
assign   source_apb = 1'b0;
assign   target_apb = 1'b0;

`endif

// generate low transfer warnings
always @(xfer_size)
begin
    less_dble = (xfer_size[15:3] == 13'h0000);
end

always @(xfer_size or less_dble)
begin
    less_word = less_dble & (xfer_size[2] == 1'b0);
end

// Generate end_xfer signal
always @(xfer_size or xfer_start or less_word or dma_read_state or 
        dma_write_state)
begin
    end_xfer = 1'b0;
    if (xfer_start & (less_word & (xfer_size[1:0] == 2'b00)))
        end_xfer = 1'b1;
    else if (~xfer_start & 
             ((dma_read_state != `idle) | (dma_write_state != `idle)))
        end_xfer = 1'b1;
end

// generate ahb_request signal - This should be asserted when in read_ahb_start
// or write_ahb_start or read_ahb_main or write_ahb_main and should be held if
// the burst signal is asserted.  It should be cleared when burst is low and
// ahb_grant and hready are both high.  It can be held only during the address
// phase. - removed burst functionality
// CANNOT REGISTER TO AVOID GLITCHS AS FUNCTIONALITY RELIES ON BEING ABLE TO 
// REMOVE REQUEST AS SOON AS GRANT ASSERTED (MAY BE ABLE TO RETHINK SLIGHTLY) 
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        iahb_req <= 1'b0;
    else if ((next_read_state == `read_ahb_main))
        iahb_req <= 1'b1;
    else if ((next_write_state == `write_ahb_start)  |
             (next_write_state == `write_ahb_main))
        iahb_req <= 1'b1;
    else if (ahb_grant & hready)
        iahb_req <= 1'b0;
end
assign ahb_req = iahb_req;

/* 
always @(iahb_req or ahb_grant or hready)
begin
    ahb_req = 1'b0;
    if (iahb_req & ~(ahb_grant & hready))
        ahb_req = 1'b1; 
end
*/
/* REPLACED BY ABOVE
always @(dma_read_state or ahb_grant or hready or dma_write_state)
begin
    ahb_req = 1'b0;
    if (((dma_read_state == `read_ahb_start)    |
          (dma_read_state == `read_ahb_main))    &
         !(ahb_grant & hready))
        ahb_req = 1'b1;
    else if (((dma_write_state == `write_ahb_start)  |
          (dma_write_state == `write_ahb_main)) &
         !(ahb_grant & hready))
        ahb_req = 1'b1;
end
*/
// Generate write_complete and write_grant signals
// These are used to provide a clean handover between reads and writes
// write_grant is asserted when the read state machine is in wait_for_write
// and write complete is asserted when the write_state machine is in 
// read_handover (doesn't leave until write_grant is removed)
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        write_grant <= 1'b0;
        write_complete <= 1'b0;
    end
    else
    begin
        write_grant <= (next_read_state == `wait_for_write);
        write_complete <= (next_write_state == `read_handover);
    end
end

// hsize control logic
// This logic will set hsize to either 1, 2 or 4 depending on the type 
// of read that has occurred, need to ensure the correct value is present
// at the end of each address cycle as it is also used to update the address
// for the following access - should know the size of each access as we
// need to use it to generate the correct hsize value for the ahb
// ASSUMPTION:  byte aligned address means byte access
//              half_word aligned means half word or byte access
//              word aligned can be any
// DEPENDANCIES:  writes with xfer_size is <4
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        hsize <= 3'b000;
    end
    else
    begin   
        if (write_grant) 
        begin   
            if (((dma_write_state == `write_ahb_start) |
                 (dma_write_state == `write_ahb_main)) &
                ahb_grant & hready)
            begin
                if (taddr[0])           // byte address
                    hsize <= `sz_byte;
                else if (taddr[1])      // half word address
                begin
                    if (xfer_size > 16'h0001)
                        hsize <= `sz_half;
                    else if (xfer_size == 16'h0001)
                        hsize <= `sz_byte;
                end
                else                    // word address
                begin
                    if (xfer_size >= 16'h0004)
                        hsize <= `sz_word;
                    else if (xfer_size > 16'h0001)
                        hsize <= `sz_half;
                    else if (xfer_size == 16'h0001)
                        hsize <= `sz_byte;
                end
            end
        end
        else
            hsize <= `sz_word;
    end
end

// hwrite control
always @(write_grant)
    hwrite = write_grant;

// Haddr control 
// The address is output when in read_ahb_staddr, read_ahb_addr, write_ahb_staddr
// write_ahb_staddr_data, write_ahb_addr or write_ahb_add_data.
always @(write_grant or saddr or taddr)
begin
    haddr = 32'h00000000;
    if (~write_grant)
        haddr = {saddr[31:2], 2'b00};
    else
        haddr = taddr;
end
// Control read/write data
// Use two pointers one for reads one for writes to cover a 36 byte buffer, 
// (allows 8 word bursts to take place) the read pointer is incremented
// with each access (assume by 4 for greedy reads) with the pointer value being
// incremented after each access.  Once reads have completed the read pointer
// is decremented by four.  The write pointer is initialised to the two lsb's
// of the source address and is then incremented on the first read access.
// The word aligned value of the new pointer is used to transfer the last
// read data into the bottom position of the buffer and the read pointer is 
// initialised to 4, the write pointer has all but the two lsb's set to zero.
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
/*        for (count=0 ; count<8 ; count=count+1)
            data_reg[count] <= 8'h00;
*/
        // always tie the top three byte positions to zero - avoids X appearing
        // in simulation when window overlaps top of buffer
        // shouldn't need for synthesis??????
        data_reg[0] <= 8'h00;
        data_reg[1] <= 8'h00;
        data_reg[2] <= 8'h00;
        data_reg[3] <= 8'h00;
        data_reg[4] <= 8'h00;
        data_reg[5] <= 8'h00;
        data_reg[6] <= 8'h00;
        data_reg[7] <= 8'h00;
        data_reg[8] <= 8'h00;
        data_reg[9] <= 8'h00;
        data_reg[10] <= 8'h00;
        write_pntr <= 3'b000;
        hwdata <= 32'h00000000;
        pwdata <= 16'h0000;
        write_count <= 2'b00;
    end
    else 
    begin
/*        //added begin
        for (count=0 ; count<8 ; count=count+1)
            data_reg[count] <= 8'h00;
	//added end
 */
        data_reg[8] <= 8'h00;
        data_reg[9] <= 8'h00;
        data_reg[10] <= 8'h00;
        // initialise write pointer at the start of each transfer
        if (dma_read_state == `idle)
        begin
            write_count <= 2'b00;
            write_pntr <= 3'b000;
            if (~source_apb)
                write_pntr[0] <= saddr[0];
            if (~source_apb)
                write_pntr[1] <= saddr[1];
        end
        // During the start state read data into bottom word and increment 
        // pointer to 4
        else if (((dma_read_state == `read_ahb_data) & hready & first_read))
        begin
            data_reg[0] <= hrdata[7:0];
            data_reg[1] <= hrdata[15:8];
            data_reg[2] <= hrdata[23:16];
            data_reg[3] <= hrdata[31:24];
        end
        // The first apb read is transferred into data_reg[0-3]
        // further reads are transferred into [4-7]
        else if ((dma_read_state == `apb_data_transfer) & source_apb )
        begin
            if (first_read)
            begin
                data_reg[0] <= temp_data0;
                data_reg[1] <= temp_data1;
                data_reg[2] <= temp_data2;
                data_reg[3] <= temp_data3;
            end
            else
            begin
                data_reg[4] <= temp_data0;
                data_reg[5] <= temp_data1;
                data_reg[6] <= temp_data2;
                data_reg[7] <= temp_data3;
            end
        end
        // When a normal access takes place load data into location 4
        // after the write shift the contents of the top word into the bottom
        // word to maintain the residue
        else if ((dma_read_state == `read_ahb_data) & hready)
        begin
            data_reg[4] <= hrdata[7:0];
            data_reg[5] <= hrdata[15:8];
            data_reg[6] <= hrdata[23:16];
            data_reg[7] <= hrdata[31:24];
        end
        // When in a valid ahb write state, output data.  Window should move
        // depending on the size of the access (use hsize)
        else if (((next_write_state == `write_ahb_stdata)        |
                  (next_write_state == `write_ahb_data)) & hready)
        begin
            hwdata[7:0]   <= data_reg[write_pntr];
            if (hsize == `sz_byte)
            begin
                write_pntr <= write_pntr + 3'b001;
                hwdata[15:8]  <= data_reg[write_pntr];
                hwdata[23:16] <= data_reg[write_pntr];
                hwdata[31:24] <= data_reg[write_pntr];
            end
            else if (hsize == `sz_half)
            begin
                write_pntr <= write_pntr + 3'h2;
                hwdata[15:8]  <= data_reg[write_pntr+3'b001];
                hwdata[23:16] <= data_reg[write_pntr];
                hwdata[31:24] <= data_reg[write_pntr+3'b001];
            end
            else if (hsize == `sz_word)
            begin
                write_pntr <= write_pntr + 3'h4;
                hwdata[15:8]  <= data_reg[write_pntr+3'b001];
                hwdata[23:16] <= data_reg[write_pntr+3'h2];
                hwdata[31:24] <= data_reg[write_pntr+3'h3];
            end
        end
        // when in a valid apb write state output data.  As in ahb case the 
        // window should move depending upon the size of access
        else if ((next_write_state == `write_apb_main))
        begin
            pwdata[7:0]  <= data_reg[write_pntr];
            pwdata[15:8] <= data_reg[write_pntr+3'b001];
        end
        else if ((next_write_state == `write_apb_data) & 
                 (~double_clk | count_two))
        begin
            if (byte_access)
            begin
                pwdata[15:8] <= data_reg[write_pntr];
                write_pntr <= write_pntr + 3'b001;
                write_count <= write_count + 2'b01;
            end
            else
            begin
                write_pntr <= write_pntr + 3'h2;
                write_count <= write_count + 2'h2;
            end
        end
        // shift new residue reg and re-init pointers
        else if ((dma_write_state == `read_handover) & ~write_grant)
        begin
            if (~first_read)
            begin
                data_reg[0] <= data_reg[4];
                data_reg[1] <= data_reg[5];
                data_reg[2] <= data_reg[6];
                data_reg[3] <= data_reg[7];
            end
            write_pntr[2] <= ~(write_pntr[1] | write_pntr[0]);
            write_count <= 2'b00;
        end
    end
end

// Need to build apb data into a word before it is transferred into the data_reg
// Use the byte_access signal to increment by either one or two for each apb 
// transfer.  This process will also generate the continue_read_apb signal - 
// this is generated irrespective of the xfer_size remaining and the read 
// state machine will ignore it if the size is zero
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        //need a read pointer for apb reads as will only get 1 or 2 bytes 
        //each read
        read_pntr  <= 2'b00;
        temp_data0 <= 8'h00;
        temp_data1 <= 8'h00;
        temp_data2 <= 8'h00;
        temp_data3 <= 8'h00;
    end
    else
    begin
        if ((dma_read_state == `read_apb_data) & (~double_clk | count_two))
        begin
            case (read_pntr)
                2'b00 :
                begin
                    temp_data0 <= prdata[7:0];
                    temp_data1 <= prdata[15:8];
                end
                2'b01 :
                begin
                    temp_data1 <= prdata[7:0];
                    temp_data2 <= prdata[15:8];
                end
                2'b10 :
                begin
                    temp_data2 <= prdata[7:0];
                    temp_data3 <= prdata[15:8];
                end
                2'b11 :
                begin
                    temp_data3 <= prdata[7:0];
                end
            endcase
            if (byte_access)
                read_pntr <= read_pntr + 2'b01;
            else
                read_pntr <= read_pntr + 2'h2;               
        end
        else if ((dma_read_state == `wait_for_write) |
                 (dma_read_state == `idle))
            read_pntr <= 2'b00;
    end
end

// generate a data_count - this will monitor the number of valid bytes held 
// in the buffer, being incremented on a read and decremented on a write
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        data_count <= 4'h0;
    end
    else
    begin
        if (dma_read_state == `idle)
            data_count <= 4'h0;
        if ((dma_read_state == `read_apb_main) & 
            (pready & (~double_clk | count_two)))
            data_count <= data_count + 4'h1 + {3'b000,~byte_access};
        else if ((dma_read_state == `read_ahb_addr) & hready)
        begin
            if (first_read)
                data_count <= 4'h4 - {2'b00,dma_sadd[1:0]};
            else
                data_count <= data_count + 4'h4;
        end
        else if ((dma_write_state == `write_apb_main) & 
                 (pready & (~double_clk | count_two)))
             if (byte_access)
               data_count <= data_count - 4'b0001;
             else
               data_count <= data_count - 4'b0010;
        else if (((dma_write_state == `write_ahb_staddr) |
                  (dma_write_state == `write_ahb_addr)) & hready)
        begin
            if (hsize == `sz_byte)
                data_count <= data_count - 4'h1;
            else if (hsize == `sz_half)
                data_count <= data_count - 4'h2;
            else if (hsize == `sz_word)
                data_count <= data_count - 4'h4;
        end
    end
end

// markrn 12/03/01 modification to fix bug
// register added to prevent continued read on apb when read_pntr overflows
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        apb_buf_full <= 1'b0;
    end
    else
    begin
        if ((dma_read_state == `read_apb_main) & (read_pntr == 2'b11))
            apb_buf_full <= 1'b1;
        else if (dma_read_state == `wait_for_write)
            apb_buf_full <= 1'b0;            
    end
end

// simplified logic term to try and fix bug
always @(xfer_size or less_word or less_dble or data_count or target_apb or
        // read_pntr or byte_access or source_apb)
         read_pntr or byte_access or source_apb or apb_buf_full)
begin
    continue_read = 1'b0;
    continue_write = 1'b0;
    if ((data_count < 4'h4) & ((data_count < xfer_size[3:0]) | ~less_dble))
        continue_read = 1'b1;
    else if (((data_count < xfer_size[3:0]) | ~less_dble) & source_apb & 
// original code
//             ((read_pntr == 2'b01) | ((read_pntr == 2'b10) & byte_access)))
// original fix 12/00
//             (!read_pntr[1] | ((read_pntr == 2'b10) & byte_access)) &
// markrn 12/03/01 modification to fix bug
// needed to add term to prevent continue read once four bytes read
             (~read_pntr[1] | (read_pntr[1] & byte_access)) &
             ~apb_buf_full)
        continue_read = 1'b1;
    if (data_count == 4'h0)
        continue_write = 1'b0;
    else if ((data_count >= xfer_size[3:0]) & less_dble)
        continue_write = 1'b1;
    else if ((data_count >= 4'h4) & ~less_word)
        continue_write = 1'b1;
    else if ((data_count >= 4'h2) & ~less_word & target_apb)
        continue_write = 1'b1;
end

// Generate byte_access signal
// byte accesses are performed when less than four bytes remain and when
// accessing circular buffers they are also performed when the source address
// is not word aligned - this means the data can alays be assumed to start at 
// data_reg[0] as the max offset is 1
// For writes they are performed when accessing a circular buffer or performing
// accesses where taddr[0] is set
// When the source is a fifo the byte_access should be set if less than 7
// bytes need to be transferred as we may only need to read 1 byte depending
// upon number written in first access (1, 2, or 3)
always @(scirc_buff or saddr or snoinc_buff or tnoinc_buff or
         tcirc_buff or taddr or write_grant or write_complete or
         read_pntr or byte_access_next or byte_access_last or dma_read_state or
         dma_write_state)
begin
    byte_access = 1'b0;
    if ((dma_read_state == `read_apb_data) | 
        (dma_write_state == `write_apb_data))
        byte_access = byte_access_last;
    else if (~write_grant)
    begin
        if (byte_access_next | scirc_buff)
            byte_access = 1'b1;
        else if (saddr[0] & ~snoinc_buff)
            byte_access = 1'b1;
        else if (read_pntr == 2'b11)
            byte_access = 1'b1;
    end
    else if (~write_complete)
    begin
        if (tcirc_buff | byte_access_next)
            byte_access = 1'b1;
        else if (taddr[0] & ~tnoinc_buff)
            byte_access = 1'b1;
    end
end

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        byte_access_next <= 1'b0;
    else
    begin
        if (~write_grant)
        begin
// markrn 09/03/01 fix to sort out uart flow control
            if (less_word)
//            if (less_dble)
                byte_access_next <= 1'b1;
            else
                byte_access_next <= 1'b0;
        end
        else if (~write_complete & (~double_clk | count_two))
        begin
            if (less_word & (xfer_size[1:0] == 2'b01))
                byte_access_next <= 1'b1;
            else
                byte_access_next <= 1'b0;
        end
        else
            byte_access_next <= 1'b0;
    end
end

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        byte_access_last <= 1'b0;
    else
    begin
        if ((dma_read_state == `read_apb_main) |
            (dma_write_state == `write_apb_main))
            byte_access_last <= byte_access;
    end
end

// Generate apb request signal
// The request should be asserted when dma_read_state = read_apb_main or
// read_apb_data or when in read_apb_hold and data is available.
// It is also raised when dma_write_state = write_apb_main or write_apb_data
//always @(next_read_state or next_write_state or data_available) Binata
always @(next_read_state or next_write_state)
begin
    apb_req_next = 1'b0;
    if ((next_read_state == `read_apb_main) | 
        (next_read_state == `read_apb_data))
        apb_req_next = 1'b1;
    else if ((next_write_state == `write_apb_main) | 
             (next_write_state == `write_apb_data))
        apb_req_next = 1'b1;
end

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        apb_req <= 1'b0;
    else
        apb_req <= apb_req_next;
end

// Generate paddr
// This should only be valid when in write_apb_main or write_apb_data but 
// should be constant for that time
// paddr needs to be more than 16 bits to ensure the psel decoding can take 
// place
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        paddr_mux <= 1'b0;
    else if ((next_read_state == `read_apb_main) | 
             (next_read_state == `read_apb_data))
        paddr_mux <= 1'b1;
    else if ((next_write_state == `write_apb_main) | 
             (next_write_state == `write_apb_data))
        paddr_mux <= 1'b0;
end

always @(paddr_mux or saddr or taddr)
begin
    paddr = 20'h0000;
    if (paddr_mux)
        paddr = saddr[19:0];
    else 
        paddr = taddr[19:0];
end 

// Generate pwrite
// this defaults to zero and is driven high during the address/data phases
// of write accesses
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        pwrite <= 1'b0;
    else if ((next_write_state == `write_apb_main) | 
             (next_write_state == `write_apb_data))
        pwrite <= 1'b1;
    else
        pwrite <= 1'b0;
end

// Generate penable
// This defaults to zero and is held high during the data phase of all accesses
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        penable <= 1'b0;
    else if ((next_read_state == `read_apb_data) |
             (next_write_state == `write_apb_data))
        penable <= 1'b1;
    else
        penable <= 1'b0;
end

// Generate count_two
// assumes hclk istwice pclk and holds the apb states for a minimum of
// two hclk cycles
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        count_two <= 1'b0;
    else if (((dma_read_state == next_read_state) & ~write_grant) |
             ((dma_write_state == next_write_state) & ~write_complete))
        count_two <= 1'b1;
    else
        count_two <= 1'b0;
end

// Need a signal to identify that an read is the first of a transfer
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        first_read <= 1'b0;
    end
    else
    begin
        if ((dma_read_state == `idle))
            first_read <= 1'b1;
        else if ((dma_read_state == `read_ahb_main) & |data_count)
            first_read <= 1'b0;
        else if ((dma_write_state == `read_handover) & ~write_grant)
            first_read <= 1'b0;
    end
end

// Generate htrans
// this should be non-seq for the first access and if any control(hsize) is 
// different otherwise it should be seq???? (need delayed version of next_size
// to enable a choice to be made on htrans (could assume all accesses are non))
always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        htrans <= `trn_idle;
    end
    else
    begin
        if (((dma_read_state == `read_ahb_main)   |
             (dma_write_state == `write_ahb_start) |
             (dma_write_state == `write_ahb_main)) & hready)
            htrans <= `trn_nonseq;
        else if (hready)
            htrans <= `trn_idle;                       
    end
end

// Control other ahb signals
// tie hburst to 3'b001 incrementing burst of unspecified length
  assign hburst = 3'b001;
// tie hprot to zero as we do not plan to use protected accesses
  assign hprot = 4'b0000;

//---------------------------
// Read state machine control
//---------------------------

dma_rx_sm i_rx_state_machine(
            .hclk           (hclk),
            .n_hreset       (n_hreset),
            .xfer_start     (xfer_start),
            .source_apb     (source_apb),
            .word_available (word_available),
            .data_available (data_available),
            .hready         (hready),
            .ahb_grant      (ahb_grant),
            .write_complete (write_complete),
            .end_xfer       (end_xfer),
            .abort          (abort),
            //.snoinc_buff    (snoinc_buff),
            .pready         (pready),
            .double_clk     (double_clk),
            .count_two      (count_two),
            //.target_apb     (target_apb),
            //.saddr          (saddr),
            //.less_word      (less_word),
            //.penable        (penable),
            .continue_read  (continue_read),
            //.data_count     (data_count),
            .less_dble      (less_dble),
            //.xfer_size      (xfer_size),
            //Outputs
            .dma_read_state (dma_read_state),
            .next_read_state(next_read_state)
            );

//---------------------------
// Write state machine control
//---------------------------

dma_tx_sm i_tx_state_machine(
            .hclk           (hclk),
            .n_hreset        (n_hreset),
            //.xfer_start     (xfer_start),// commented by Binata
            //.source_apb     (source_apb),// commented by Binata
            .write_grant    (write_grant),
            .slot_available (slot_available),
            .hready         (hready),
            .ahb_grant      (ahb_grant),
            .end_xfer       (end_xfer),
            .abort          (abort),
            .target_apb     (target_apb),
            .taddr          (taddr[1]),
            .pready         (pready),
            .double_clk     (double_clk),
            //.penable        (penable),
            .continue_write (continue_write),
            .count_two      (count_two),
            //Outputs
            .dma_write_state(dma_write_state),
            .next_write_state(next_write_state)
            );


endmodule
