//File name   : req_register.v
//Title       : 
//Created     : 1999
//Description : This module registers AHB bus access requests from various AHB masters,
//              decodes the target slave and puts request for accessing that slave.
//              It also generates HRESP and HREADY responses to requesting AHB bus master 
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
module req_register (

    // input ports 
    
    hclk,
    hresetn,
    hsel,
    haddr,
    htrans,
    hwrite,
    hsize,
    hburst,
    hprot,
    hready,
    gnt,
    hready_out_from_slave,
    hresp_from_slave,
   

   // output ports
   haddr_out,
   htrans_out,
   hwrite_out,
   hsize_out,
   hburst_out,
   hprot_out,
   hresp_out,
   hready_out,
   data_gnt,
   master_sel

);

`include "bm_defs.v"
`include "bm_params.v"


input hclk;         // clk input
input hresetn;      // Reset
input hsel;         // hsel from bus master
input [`AHB_ADDR_WIDTH - 1 : 0] haddr;   // HADDR from bus master
input [1:0] htrans;  //  HTRANS from bus master
input hwrite;        //  HWRITE from bus master
input [2 : 0] hsize; // HSIZE from bus master
input [2 : 0] hburst; // HBURST from bus master
input [3 : 0] hprot;  // HPROT from bus master
input hready;        // HREADY from bus master
input [`NUM_OF_MASTERS - 1 : 0] gnt; // Grant from masters
input hready_out_from_slave;   // hready from selected master interface
input [1 : 0] hresp_from_slave;        // hresp from selected slave

output [`AHB_ADDR_WIDTH - 1 : 0] haddr_out; // HADDR
output [1:0] htrans_out;                    // HTRANS
output hwrite_out;                          // HWRITE
output [2 : 0] hsize_out;                   // HSIZE
output [2 : 0] hburst_out;                  // HBURST
output [3 : 0] hprot_out;                   // HPROT
output [1 : 0] hresp_out;                   // HRESP
output hready_out;                          // HREADY

output data_gnt;
output [`NUM_OF_MASTERS - 1 : 0] master_sel;


reg [`AHB_ADDR_WIDTH - 1 : 0] haddr_out;
reg [1:0] htrans_out;
reg hwrite_out;
reg [2 : 0] hsize_out;
reg [2 : 0] hburst_out;
reg [3 : 0] hprot_out;
reg [1 : 0] hresp_out;
reg hready_out;
reg hsel_out;
wire [`NUM_OF_MASTERS - 1 : 0] master_sel;

reg [`AHB_ADDR_WIDTH - 1 : 0] haddr_r;
reg [1:0] htrans_r;
reg hwrite_r;
reg [2 : 0] hsize_r;
reg [2 : 0] hburst_r;
reg [3 : 0] hprot_r;
reg hsel_r;
reg hready_r;
reg hready_in;

wire new_tran;
wire addr_phase;
reg  store_tran;
wire seq_tran;
reg [`NUM_OF_MASTERS - 1 : 0] data_gnt; // Grant from masters

wire stored_new_tran, bus_new_tran;
wire back2back;
reg seq_or_non_seq_tr;

// Detect a stored new transaction 
assign stored_new_tran = store_tran && (hsel_out  & (htrans_out == `NON_SEQ) );

// Detect a new transaction on AHB bus
assign bus_new_tran = (hsel & hready & (htrans == `NON_SEQ) );

// Detect a sequential transaction on AHB bus
assign seq_tran = hsel &&   ( (htrans == `SEQ) || (htrans == `BUSY) ); 


always @ (posedge hclk or negedge hresetn)
  if (~hresetn)
    seq_or_non_seq_tr <= 1'b0;
  else if ( (seq_tran && hready) || bus_new_tran )
    seq_or_non_seq_tr <=  1'b1;
  else 
    seq_or_non_seq_tr <= 1'b0;


assign back2back = seq_or_non_seq_tr && bus_new_tran;


// store_tran is a flag which indicates transaction is stored as master is busy
// store_tran = 1, indicates transaction is waiting for master to be available
always @ (posedge hclk or negedge hresetn)
  if (~hresetn)
    store_tran <= 1'b0;
  else
    if (bus_new_tran & ( ~|gnt  || back2back ) )
      store_tran <= 1'b1;
    else if (store_tran & |gnt & hready_out_from_slave)
      store_tran <= 1'b0;
 
 


// Register all details related to transaction as it will not be available
// on bus when master is available
always @ (posedge hclk or negedge hresetn)

  if (~hresetn)
   begin
     hsel_r   <= 1'b0;
     haddr_r  <= `AHB_ADDR_WIDTH'b0;
     htrans_r <= 2'b0;
     hwrite_r <= 1'b0;
     hsize_r  <= 1'b0;
     hburst_r <= 3'b0;
     hprot_r  <= 4'b0;
     hready_r <= 1'b1;
   end
  else if (bus_new_tran)
   begin
     hsel_r   <= hsel;
     haddr_r  <= haddr;
     htrans_r <= htrans;
     hwrite_r <= hwrite;
     hsize_r  <= hsize;
     hburst_r <= hburst;
     hprot_r  <= hprot;
     hready_r <= hready;
   end


// If stored transaction is waiting, use registered version of transaction details
// else use directly from input bus.
always @*

  if (store_tran)
   begin
     hsel_out   = hsel_r;
     haddr_out  = haddr_r;
     htrans_out = htrans_r;
     hwrite_out = hwrite_r;
     hsize_out  = hsize_r;
     hburst_out = hburst_r;
     hprot_out  = hprot_r;
     hready_in =  hready_r;
   end
  else
   if (back2back)
     begin
       hsel_out   = 1'b0; 
       haddr_out  = haddr;
       htrans_out = `IDLE;
       hwrite_out = hwrite;
       hsize_out  = hsize;
       hburst_out = hburst;
       hprot_out  = hprot;
       hready_in =  hready;
     end
    else
      begin
        hsel_out   = hsel; 
        haddr_out  = haddr;
        htrans_out = htrans;
        hwrite_out = hwrite;
        hsize_out  = hsize;
        hburst_out = hburst;
        hprot_out  = hprot;
        hready_in =  hready;
      end

   

// generate responses

// The following generates HRESP and HREADY to originating bus master 
// 1> If stored transaction is waiting for access to bus master interface
// it drive HREADY LOW

// 2> When originating master is IDLE drive HREADY -  HIGH

// 3> During data_phase of any transaction drive actual responses from slave
always @*
  begin
      hresp_out = `OKAY;
      hready_out = 1'b1;
    if (store_tran)
     begin
      hresp_out = `OKAY;
      hready_out = 1'b0;
     end
    else if (|data_gnt)
     begin
      hresp_out = hresp_from_slave;
      hready_out = hready_out_from_slave;
     end
    else if (~store_tran & ~|gnt )
     begin
      hresp_out = `OKAY;
      hready_out = 1'b1;
     end
  end 



// Register a grant during address phase, this is required to multiplex hrdata, 
// hresp and hready from selected master interface.
always @ (posedge hclk or negedge hresetn)
  if (~hresetn)
    data_gnt <= `NUM_OF_MASTERS'b0;
  else if (addr_phase && |gnt && hready_out_from_slave)
    data_gnt <= gnt;
  else if (hready_out_from_slave)
    data_gnt <= `NUM_OF_MASTERS'b0;
    

assign addr_phase = hsel_out &&  (htrans_out != `IDLE) && (htrans_out != `BUSY);




// These master_sel are directly connected to req inputs to master interfaces
// To access a particular targrt slave, address range should fall in that range.
// Apart from address following condition should meet,
// 1. New transaction is available on AHB bus
// 2. Stored new transaction is waiting for bus access without grant
// 3. Sequential transaction is available with grant already given.

`ifdef MASTER0
assign master_sel[0] =  ( bus_new_tran || ( stored_new_tran && ~gnt[0]) || (seq_tran && gnt[0]) ) && (haddr_out >=  SLAVE0_START_ADDR) && (haddr_out <= SLAVE0_END_ADDR);
`endif

`ifdef MASTER1
assign master_sel[1] =  ( bus_new_tran || ( stored_new_tran && ~gnt[1]) || (seq_tran && gnt[1]) ) && (haddr_out >=  SLAVE1_START_ADDR) && (haddr_out <= SLAVE1_END_ADDR);
`endif

`ifdef MASTER2
assign master_sel[2] =  ( bus_new_tran || ( stored_new_tran && ~gnt[2]) || (seq_tran && gnt[2]) ) && (haddr_out >=  SLAVE2_START_ADDR) && (haddr_out <= SLAVE2_END_ADDR);
`endif

`ifdef MASTER3
assign master_sel[3] =  ( bus_new_tran || ( stored_new_tran && ~gnt[3]) || (seq_tran && gnt[3]) ) && (haddr_out >=  SLAVE3_START_ADDR) && (haddr_out <= SLAVE3_END_ADDR);
`endif

`ifdef MASTER4
assign master_sel[4] =  ( bus_new_tran || ( stored_new_tran && ~gnt[4]) || (seq_tran && gnt[4]) ) && (haddr_out >=  SLAVE4_START_ADDR) && (haddr_out <= SLAVE4_END_ADDR);
`endif

`ifdef MASTER5
assign master_sel[5] =  ( bus_new_tran || ( stored_new_tran && ~gnt[5]) || (seq_tran && gnt[5]) ) && (haddr_out >=  SLAVE5_START_ADDR) && (haddr_out <= SLAVE5_END_ADDR);
`endif

`ifdef MASTER6
assign master_sel[6] =  ( bus_new_tran || ( stored_new_tran && ~gnt[6]) || (seq_tran && gnt[6]) ) && (haddr_out >=  SLAVE6_START_ADDR) && (haddr_out <= SLAVE6_END_ADDR);
`endif

`ifdef MASTER7
assign master_sel[7] =  ( bus_new_tran || ( stored_new_tran && ~gnt[7]) || (seq_tran && gnt[7]) ) && (haddr_out >=  SLAVE7_START_ADDR) && (haddr_out <= SLAVE7_END_ADDR);
`endif

`ifdef MASTER8
assign master_sel[8] =  ( bus_new_tran || ( stored_new_tran && ~gnt[8]) || (seq_tran && gnt[8]) ) && (haddr_out >=  SLAVE8_START_ADDR) && (haddr_out <= SLAVE8_END_ADDR);
`endif

`ifdef MASTER9
assign master_sel[9] =  ( bus_new_tran || ( stored_new_tran && ~gnt[9]) || (seq_tran && gnt[9]) ) && (haddr_out >=  SLAVE9_START_ADDR) && (haddr_out <= SLAVE9_END_ADDR);
`endif

`ifdef MASTER10
assign master_sel[10] = ( bus_new_tran || ( stored_new_tran && ~gnt[10]) || (seq_tran && gnt[10]) ) && (haddr_out >= SLAVE10_START_ADDR) && (haddr_out <= SLAVE10_END_ADDR);
`endif

`ifdef MASTER11
assign master_sel[11] = ( bus_new_tran || ( stored_new_tran && ~gnt[11]) || (seq_tran && gnt[11]) ) && (haddr_out >= SLAVE11_START_ADDR) && (haddr_out <= SLAVE11_END_ADDR);
`endif

`ifdef MASTER12
assign master_sel[12] = ( bus_new_tran || ( stored_new_tran && ~gnt[12]) || (seq_tran && gnt[12]) ) && (haddr_out >= SLAVE12_START_ADDR) && (haddr_out <= SLAVE12_END_ADDR);
`endif

`ifdef MASTER13
assign master_sel[13] = ( bus_new_tran || ( stored_new_tran && ~gnt[13]) || (seq_tran && gnt[13]) ) && (haddr_out >= SLAVE13_START_ADDR) && (haddr_out <= SLAVE13_END_ADDR);
`endif

`ifdef MASTER14
assign master_sel[14] = ( bus_new_tran || ( stored_new_tran && ~gnt[14]) || (seq_tran && gnt[14]) ) && (haddr_out >= SLAVE14_START_ADDR) && (haddr_out <= SLAVE14_END_ADDR);
`endif

`ifdef MASTER15
assign master_sel[15] = ( bus_new_tran || ( stored_new_tran && ~gnt[15]) || (seq_tran && gnt[15]) ) && (haddr_out >= SLAVE15_START_ADDR) && (haddr_out <= SLAVE15_END_ADDR);
`endif


endmodule

 
   
