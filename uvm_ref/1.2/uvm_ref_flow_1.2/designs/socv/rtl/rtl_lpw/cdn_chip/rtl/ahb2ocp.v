//File name   : ahb2ocp.v
//Title       : 
//Created     : 1999
//Description : Bridge b/w AHB master and sCp slave.
//              write data is stored in a fifo(32 deep - 512bytes) before
//              being burst on the ocp bus.
//              data write is expected to start at 16byte boundary
//              (haddr[3:0] = 0). data can be filled into the fifo in 
//              smaller chunks but it should be continous data. 
//              fifo depth is programmable.
//              Read support is only for a single 32 bit read.
//Notes       : 
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

`include "ahb2ocp_defs.v"

module ahb2ocp(


              n_preset, 
              pclk, 
              ao_psel_i, 
              ao_penable_i, 
              ao_pwrite_i, 
              ao_paddr_i, 
              ao_pwdata_i,


              hclk,
              n_hreset,

              ao_hsel_i,
	           ao_haddr_i,
	           ao_htrans_i,
	           ao_hsize_i,
	           ao_hburst_i,
	           ao_hprot_i,
	           ao_hwdata_i,
	           ao_hwrite_i,
              ao_hready_i,

              ao_sdata_i,
              ao_sresp_i,
              ao_sresplast_i,

              ao_scmdaccept_i,
              ao_sdataaccept_i,


              ao_prdata_o,

	           ao_hrdata_o,
	           ao_hready_o,
	           ao_hresp_o,

              ao_mcmd_o,
              ao_maddr_o,
              ao_matomic_length_o,
              ao_mburst_precise_o,
              ao_mburst_single_req_o,
              ao_mburstlength_o,
              ao_mburst_seq_o,
              ao_mtag_id_o,
              ao_mdata_tag_id_o,
              ao_mdata_o,
              ao_mdatalast_o,
              ao_mdatavalid_o,
              ao_mdataaccept_o,
              ao_mrespaccept_o
              );

//-------------------Parameter Declarations-----------------------------------//
parameter OCP_DATA_WIDTH = 128; //OCP DATA
parameter OCP_ADDR_WIDTH = 28;  //OCP ADDR

parameter FF_DEPTH  =  'd32 ;//'h8;
parameter FFADD_WIDTH = 'h5 ;//'h3;

parameter OCP_MTAG  = 3'h1;
parameter OCP_MDATA_TAG  = 3'h1;

parameter IDLE   = 3'h0;
parameter MCMD_WR   = 3'h1;
parameter WAIT    = 3'h2;
parameter MCMD_RD   = 3'h3;
parameter SDATA   = 3'h4;
parameter HDATA   = 3'h5;

parameter DATA_WIDTH = OCP_DATA_WIDTH;
parameter ADDR_WIDTH = OCP_ADDR_WIDTH;

//-------------------Port Declarations----------------------------------------//
  input        n_preset;           // APBreset 
  input        pclk;               // APB clock
  input        ao_psel_i;               // APB select
  input        ao_penable_i;            // APB enable 
  input        ao_pwrite_i;             // APB write strobe 
  input [4:0]  ao_paddr_i;              // APB address bus
  input [31:0] ao_pwdata_i;             // APB write data 
  output[31:0] ao_prdata_o;             // APB write data 


   input          hclk;
   input          n_hreset;

	input        	        ao_hsel_i; //slave select
	input [31:0]  	        ao_haddr_i; 
	input [1:0]  	        ao_htrans_i; //IDLE,BUSY,NONSEQ,SEQ
	input [2:0]  	        ao_hsize_i;  //byte, halfword, word ....
	input [2:0]  	        ao_hburst_i; //SINGLE,INCR,WR4,INCR4,WR8,IN8,WR16,IN16
	input [3:0]  	        ao_hprot_i;
	input [31:0]  	        ao_hwdata_i;
	input		              ao_hwrite_i;
   input                  ao_hready_i;

   input                  ao_scmdaccept_i;
   input                  ao_sdataaccept_i;
   input [DATA_WIDTH-1:0]  ao_sdata_i; //128 bit
   input [1:0]            ao_sresp_i; //NULL, DVA, FAIL, ERR
   input                  ao_sresplast_i;

	output [31:0] 	        ao_hrdata_o;
	output        	        ao_hready_o;
	output [1:0]           ao_hresp_o; //OKAY,ERROR,RETRY,SPLIT

   output [2:0]           ao_mcmd_o; //idle. write,read,readex...
   output [ADDR_WIDTH-1:0] ao_maddr_o; //28 bit
   output  [4:0]          ao_matomic_length_o;
   output                 ao_mburst_precise_o;
   output                 ao_mburst_single_req_o;
   output [4:0]           ao_mburstlength_o; 
   output [2:0]           ao_mburst_seq_o;//INCR,DFLT1,WRAP,DFLT2,XOR,STRM,UNKN,BLK
   output [DATA_WIDTH-1:0] ao_mdata_o; //128 bit write data on OCP I/F
   output                 ao_mdatalast_o;
   output                 ao_mdatavalid_o;
   output                 ao_mdataaccept_o;
   output                 ao_mrespaccept_o;

   output [2:0]           ao_mtag_id_o;
   output [2:0]           ao_mdata_tag_id_o;
//---------------Internal register declarations-------------------------------//
`ifndef FV_KIT_BLACK_BOX_OCPB 

wire        ahb_valid;
wire[FFADD_WIDTH-1:0]   fifo_addr;
wire        fifo_full, fifo_mt, fifo_rd, fifo_wr, fifo_clr;
wire[127:0] fifo_data, fifo_rd_data;
wire [20:0] half_count; //dpends of the fifo depth. used to indicate half-count.


reg         ahb_write; // 1 clk delayed of hwrite - write data cyle.
reg [127:0] buffer, rd_buffer;
                  //4 words of 32 bit each.
reg [2:0]   state, nxt_state;
reg [20:0]  offset_addr,maddr_cnt;
reg [3:0]   addr_lat;
reg         buffer_rdy, fifo_rdy;
reg [FFADD_WIDTH-1:0]   fifo_wr_cnt, fifo_rd_cnt, resp_cnt;
reg         ao_mdatavalid_o;
reg [31:0] ao_hrdata_o;
reg        buffer_mt;
//APB registers related
reg [ADDR_WIDTH -1:0]  base_addr_reg;
reg [FFADD_WIDTH :0]   ff_depth_reg;
reg                    fifo_ctrl_reg;
reg [31:0]             ao_prdata_o;

reg                    fifo_ctrl_reg_d;
wire                   fifo_clr_sw;
reg                    err_resp;
//----------------CODE--------------------------------------------------------//
//wire [31:0] base_addr_reg = 32'h0080_0000; //to be removed
//wire [FFADD_WIDTH:0] ff_depth_reg = 'd32; //'d8; //'d32; // 'd8; //to be removed
//wire  fifo_clr_reg   = 1'b0;   //to be removed

assign half_count = (ff_depth_reg >> 1) -1; //mburstlength = 'h2

assign ahb_valid = ao_htrans_i[1] & ao_hsel_i &  ao_hready_i & ao_hready_o ;

always @(posedge hclk or negedge n_hreset) begin
  if (~n_hreset) begin
	 ahb_write     <= 1'b0;
    buffer        <= 'h0;
    buffer_rdy    <= 'h0;
    offset_addr   <= 'h0;
    addr_lat      <= 'h0;
    state         <= IDLE;
    fifo_wr_cnt   <= 'h0;
    fifo_rd_cnt   <= 'h0;
    fifo_rdy      <= 1'b0;
    fifo_ctrl_reg_d <= 1'b0;
    maddr_cnt      <= 'h0;
    ao_mdatavalid_o <= 1'b0;
    buffer_mt     <= 1'b1;

    rd_buffer     <= 'h0;
    err_resp      <= 'h0;
    resp_cnt      <= 'h0;

  end 
  else begin
    ahb_write <= ao_hwrite_i & ahb_valid;
    state  <= nxt_state;
    fifo_ctrl_reg_d <= fifo_ctrl_reg;

    if(fifo_rd) ao_mdatavalid_o <= 1'b1;
    else if(fifo_mt & ao_sdataaccept_i) ao_mdatavalid_o <= 1'b0; 

    if(ahb_valid) addr_lat <= ao_haddr_i[3:0];


    if(ao_hwrite_i & ahb_valid ) buffer_mt <= 1'b0;
    else if(fifo_rdy) buffer_mt <= 'h1;

    //offset addr is is the first address on any valid AHB access. 
    //Must be 16byte word aligned
    if(buffer_mt & ahb_valid) offset_addr <= ao_haddr_i[20:0]; 
    
    if(fifo_clr) fifo_wr_cnt <= 'h0;
    else if(fifo_wr) fifo_wr_cnt <= fifo_wr_cnt + 1'b1;

    if(fifo_clr) fifo_rd_cnt <= 'h0;
    else if(fifo_rd) fifo_rd_cnt <= fifo_rd_cnt + 1'b1;

    if((fifo_wr_cnt == ff_depth_reg-1) & fifo_wr) fifo_rdy <= 1'b1;
    else if(fifo_clr) fifo_rdy <= 1'b0;

    //maddr_cnt is used since mburstlength is 2  and hence 32 byte addressing is
    // needed on OCP side
    if((state == MCMD_WR) & ao_scmdaccept_i) maddr_cnt <= maddr_cnt + 1'b1;
    else if(buffer_mt & ahb_valid) maddr_cnt <= 'h0;

    if(ao_sresplast_i & ((state == MCMD_WR) | (state == WAIT))) resp_cnt <= resp_cnt + 1'b1;
    else if(state == IDLE) resp_cnt <= 'h0;


    if(ahb_write) begin
      case(addr_lat[3:2])
      2'h0 : 
      begin
        buffer[31:0]   <= ao_hwdata_i;
        buffer_rdy     <= 1'b0;
      end
      2'h1 : 
      begin
        buffer[63:32]  <= ao_hwdata_i;
        buffer_rdy     <= 1'b0;
      end
      2'h2 : 
      begin
        buffer[95:64]  <= ao_hwdata_i;
        buffer_rdy     <= 1'b0;
      end
      2'h3 : 
      begin
        buffer[127:96] <= ao_hwdata_i;
        buffer_rdy     <= 1'b1;
      end
      endcase
    end
    else begin
      buffer_rdy <= 1'b0;
    end


    if((state == SDATA) & (nxt_state == HDATA) & (ao_sresp_i == 'h1))
      rd_buffer <= ao_sdata_i;

    if((state == SDATA) & (nxt_state == HDATA) & (ao_sresp_i[1] == 'h1))
      err_resp <= 1'b1;
    else err_resp <= 1'b0;

  end
end

assign fifo_full = (fifo_rd_cnt == 'h0) & (fifo_wr_cnt == 'h0) & fifo_rdy;
assign fifo_mt   = (fifo_rd_cnt == 'h0) & (fifo_wr_cnt == 'h0) & ~fifo_rdy;

assign fifo_wr = buffer_rdy;
assign fifo_data = buffer;
assign fifo_addr = fifo_rdy ?fifo_rd_cnt: fifo_wr_cnt;

assign fifo_rd = fifo_rdy ;//& ao_sdataaccept_i;
assign fifo_clr = (((fifo_rd_cnt == ff_depth_reg-1) & fifo_rd) | fifo_clr_sw);

assign fifo_clr_sw = fifo_ctrl_reg & ~fifo_ctrl_reg_d;

//OCP CMD FSM
always @(*)
begin
  nxt_state = state;
  case (state)
  IDLE :
  begin
    if(buffer_rdy) nxt_state = MCMD_WR;
    else if(ahb_valid & ~ao_hwrite_i) nxt_state = MCMD_RD;
  end
  MCMD_WR :
  begin
    if(ao_scmdaccept_i) begin
       if(maddr_cnt == half_count) nxt_state = WAIT; 
    end
    else nxt_state = MCMD_WR;
  end
  WAIT:
  begin
    if(ao_sresplast_i) begin
      if(fifo_mt & (resp_cnt == half_count)) nxt_state = IDLE;
    end
    else nxt_state = WAIT;
  end
  MCMD_RD:
  begin
    if(ao_scmdaccept_i) nxt_state = SDATA; 
    else nxt_state = MCMD_RD;
  end
  SDATA:
  begin
    if(ao_sresp_i != 'h0) nxt_state = HDATA; 
    else nxt_state = SDATA;
  end
  HDATA:
  begin
    nxt_state = IDLE;
  end

  endcase
end


//addressing is 16byte word aligned
assign ao_maddr_o = (state == MCMD_WR)? base_addr_reg + offset_addr + {maddr_cnt,5'h0}: 
                    (state == MCMD_RD)? base_addr_reg + {offset_addr[20:4], 4'h0} : 'h0;
assign ao_mcmd_o  = (state == MCMD_WR)? 3'b001: 
                    (state == MCMD_RD)? 3'b010: 3'b000;
assign ao_matomic_length_o = 4'h2;
assign ao_mburst_precise_o = 1'b1;
assign ao_mburstlength_o = 'h2;
assign ao_mburst_seq_o  = 3'b000;
assign ao_mburst_single_req_o  = 1'b1;
assign ao_mdata_o = fifo_rd_data; 
assign ao_mdatalast_o = ao_mdatavalid_o & ~fifo_rd_cnt[0];
assign ao_mdataaccept_o = 1'b1;
assign ao_mrespaccept_o = 1'b1;
assign ao_mtag_id_o   = OCP_MTAG;
assign ao_mdata_tag_id_o   = OCP_MDATA_TAG;

assign ao_hready_o = ~(fifo_rdy | ((fifo_wr_cnt == ff_depth_reg-1) & buffer_rdy) | 
                      ((fifo_wr_cnt == ff_depth_reg-1) & (addr_lat[3:2] == 2'b11) & ahb_write) |
                      ((state == WAIT) & fifo_mt) | (ao_mdatavalid_o) |
                      (state == MCMD_RD) | (state == SDATA)); 
assign ao_hresp_o  = ((state == SDATA) & (nxt_state == HDATA) & (ao_sresp_i[1] == 'h1)) 
                      |err_resp ? 2'h1 : 2'h0; 

always @ (*)
begin
  ao_hrdata_o = 'h0;
  if(state == HDATA) begin
    case(addr_lat[3:2])
    2'h0: ao_hrdata_o = rd_buffer[31:0];
    2'h1: ao_hrdata_o = rd_buffer[63:32];
    2'h2: ao_hrdata_o = rd_buffer[95:64];
    2'h3: ao_hrdata_o = rd_buffer[127:96];
    endcase
  end
  else begin
    ao_hrdata_o = 'h0;
  end
end


`ifdef ASIC_SYNTHESIS

`else
     ahb2ocp_ram #(32,128,5) U_ocp_buf(
             .clk       (hclk),
             .rst_n     (n_hreset),
             .rd_e      (fifo_rd), 
             .addr      (fifo_addr),
             .rdata     (fifo_rd_data),
             .wr_e      (fifo_wr),
             .wdata     (fifo_data),
             .be        ({128{1'b1}}),
             .cs        (1'b1)
          );
`endif

//Register programming through APB BUS
           
always @ (*) begin
  ao_prdata_o = 32'h0;
  if(ao_psel_i & ao_penable_i) begin
     case (ao_paddr_i)
     `BASE_ADDR_ADDR  : ao_prdata_o = base_addr_reg;
     `FIFO_DEPTH_ADDR : ao_prdata_o = ff_depth_reg;
     `FIFO_CTRL_ADDR  : ao_prdata_o = fifo_ctrl_reg;
     `FIFO_STS_ADDR   : ao_prdata_o = {30'h0,fifo_full, fifo_mt};
      default         : ao_prdata_o = 32'h0;
     endcase
  end
  else ao_prdata_o = 32'h0;
end

always @(posedge pclk or negedge n_preset) begin
  if(~n_preset) begin
    base_addr_reg     <= `BASE_ADDR_DEF;
    ff_depth_reg      <= `FIFO_DEPTH_DEF;
    fifo_ctrl_reg     <= 'h0;
  end
  else begin
    if(ao_psel_i & ao_penable_i & ao_pwrite_i) begin
      case (ao_paddr_i )
     `BASE_ADDR_ADDR  : base_addr_reg  <= ao_pwdata_i[ADDR_WIDTH -1:0];
     `FIFO_DEPTH_ADDR : ff_depth_reg   <= ao_pwdata_i[FFADD_WIDTH:0];
     `FIFO_CTRL_ADDR  : fifo_ctrl_reg  <= ao_pwdata_i[0];
      endcase
    end
  end
end



`ifdef OCP_ABVIP_ON
// psl constraint_base_addr : assume
// always (base_addr_reg == `BASE_ADDR_DEF)
// ;

// psl constraint_ff_depth : assume
// always (ff_depth_reg == 2)
// ;

// psl constraint_ff_ctrl : assume
// always (fifo_ctrl_reg == 0)
// ;

// psl constraint_offset_addr : assume
// always (offset_addr[4:0] == 5'b0)
// ;

reg [3:0] nxt_addr_lat;
always @ (posedge hclk or negedge n_hreset) begin
  if  (~n_hreset)
    nxt_addr_lat <= 4'b0;
  else if (ahb_valid & ao_hwrite_i)
    nxt_addr_lat <= nxt_addr_lat + 4;
  end


reg [1:0] wr_counter;
always @ (posedge hclk or negedge n_hreset) begin
  if  (~n_hreset)
    wr_counter <= 2'b0;
  else if (ahb_valid & ao_hwrite_i)
    wr_counter <= wr_counter + 1;
end



// nopsl new_10 : assume 
// always ( (ahb_valid & ao_hwrite_i & (wr_counter != 3) ) -> next (ao_htrans_i[1] & ao_hsel_i &  ao_hready_i  & ao_hwrite_i) );


// psl constraint_write_incr_addr : assume 
// always (ahb_valid & ao_hwrite_i) -> (ao_haddr_i[3:0] == nxt_addr_lat);

// psl constraint_hburst : assume 
// always (ao_hburst_i == 3'b011);

// psl constraint_hsize : assume 
// always (ao_hsize_i == 3'b010);

`endif



`else
//------------------------------------------------------------------------------
// if OCPB is black boxed 
//------------------------------------------------------------------------------

  wire         n_preset;           // APBreset 
  wire         pclk;               // APB clock
  wire         ao_psel_i;               // APB select
  wire         ao_penable_i;            // APB enable 
  wire         ao_pwrite_i;             // APB write strobe 
  wire  [4:0]  ao_paddr_i;              // APB address bus
  wire  [31:0] ao_pwdata_i;             // APB write data 
  reg   [31:0] ao_prdata_o;             // APB write data 


   wire           hclk;
   wire           n_hreset;

	wire         	        ao_hsel_i; //slave select
	wire  [31:0]  	        ao_haddr_i; 
	wire  [1:0]  	        ao_htrans_i; //IDLE,BUSY,NONSEQ,SEQ
	wire  [2:0]  	        ao_hsize_i;  //byte, halfword, word ....
	wire  [2:0]  	        ao_hburst_i; //SINGLE,INCR,WR4,INCR4,WR8,IN8,WR16,IN16
	wire  [3:0]  	        ao_hprot_i;
	wire  [31:0]  	        ao_hwdata_i;
	wire 		              ao_hwrite_i;
   wire                   ao_hready_i;

   wire                   ao_scmdaccept_i;
   wire                   ao_sdataaccept_i;
   wire  [DATA_WIDTH-1:0]  ao_sdata_i; //128 bit
   wire  [1:0]            ao_sresp_i; //NULL, DVA, FAIL, ERR
   wire                   ao_sresplast_i;

	reg    [31:0] 	        ao_hrdata_o;
	reg           	        ao_hready_o;
	reg    [1:0]           ao_hresp_o; //OKAY,ERROR,RETRY,SPLIT

   reg    [2:0]           ao_mcmd_o; //idle. write,read,readex...
   reg    [ADDR_WIDTH-1:0] ao_maddr_o; //28 bit
   reg     [4:0]          ao_matomic_length_o;
   reg                    ao_mburst_precise_o;
   reg                    ao_mburst_single_req_o;
   reg    [4:0]           ao_mburstlength_o; 
   reg    [2:0]           ao_mburst_seq_o;//INCR,DFLT1,WRAP,DFLT2,XOR,STRM,UNKN,BLK
   reg    [DATA_WIDTH-1:0] ao_mdata_o; //128 bit write data on OCP I/F
   reg                    ao_mdatalast_o;
   reg                    ao_mdatavalid_o;
   reg                    ao_mdataaccept_o;
   reg                    ao_mrespaccept_o;

`endif




endmodule
