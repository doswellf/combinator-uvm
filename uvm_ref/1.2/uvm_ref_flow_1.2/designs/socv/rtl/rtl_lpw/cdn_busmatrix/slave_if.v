//File name   : slave_if.v
//Title       : 
//Created     : 1999
//Description : This is a Slave interface module, it detects AHB transactions on the
//              bus, places a request to selected master interface for AHB bus access,
//              holds the transaction details as long as master interface is busy.
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

module slave_if (

   // input ports
   hclk,
   hresetn,
   hsel,     // HSEL from AHB master
   haddr,    // HADDR from AHB master
   htrans,   // HTRANS from AHB master
   hwrite,   // HWRITE from AHB master
   hsize,    // HSIZE from AHB master
   hburst,   // HBURST from AHB master
   hprot,    // HPROT from AHB master
   hready,   // HREADY from AHB master

   gnt,   // From master interface
   s_hresp_from_all_slave,   // From master interface
   s_hready_from_all_slave,  // From master interface
   s_hrdata_from_all_slave,  // From master interface

   // output ports
   hresp_out,   // HRESP from selected master interface to AHB master
   hready_out,  // HREADY from selected master interface to AHB master
   hrdata_out,  // HRDATA from selected master interface to AHB master
   haddr_int,   // HADDR to master interfaces
   htrans_int,  // HTRANS to master interfaces
   hwrite_int,  // HWRITE to master interfaces
   hsize_int,   // HSIZE to master interfaces
   hburst_int,  // HBURST to master interfaces
   hprot_int,   // HPROT to master interfaces
   
   req          // Request to master interfaces

);

`include "bm_defs.v"

// TODO : put ifdefs
// TODO : put comments


// These are main inputs from actual AHB master
input  hclk;
input  hresetn;
input  hsel;
input  [`AHB_ADDR_WIDTH - 1 : 0] haddr;
input  [1:0] htrans;
input  hwrite;
input  [2:0] hsize;
input  [2:0] hburst;
input  [3:0] hprot;
input  hready;

input [`NUM_OF_MASTERS - 1: 0] gnt;   // From master interface
input [`NUM_OF_MASTERS * 2 - 1 :0] s_hresp_from_all_slave;
input [`NUM_OF_MASTERS - 1 : 0] s_hready_from_all_slave;
input [`NUM_OF_MASTERS * `AHB_DATA_WIDTH - 1 : 0] s_hrdata_from_all_slave;

output [1:0] hresp_out;
output hready_out;
output [`AHB_DATA_WIDTH - 1 : 0] hrdata_out;
output  [`AHB_ADDR_WIDTH - 1 : 0] haddr_int;
output  [1:0] htrans_int;
output hwrite_int;
output  [2:0] hsize_int;
output  [2:0] hburst_int;
output  [3:0] hprot_int;

output [`NUM_OF_MASTERS - 1: 0] req;

wire [1:0] hresp_out;
wire hready_out;
wire [`AHB_DATA_WIDTH - 1 : 0] hrdata_out;
wire [1 : 0] hresp_from_slave;
wire  hready_out_from_slave;

wire  [`AHB_ADDR_WIDTH - 1 : 0] haddr_int;
wire  [1:0] htrans_int;
wire hwrite_int;
wire  [2:0] hsize_int;
wire  [2:0] hburst_int;
wire  [3:0] hprot_int;

wire [`NUM_OF_MASTERS - 1: 0] req;
wire [`NUM_OF_MASTERS - 1: 0] data_gnt;   

wire [2:0] mux_out;
wire [`AHB_DATA_WIDTH - 1 : 0] data_mux_out;

// HRESP, HREADY and HRDATA from various master interfaces are 
// concatenated and given to slave interface in terms of 
// "s_hresp_from_all_slave", "s_hready_from_all_slave" and 
// "s_hrdata_from_all_slave"

// Slave interface seperates these responses depending on Master 
// interface which generated it and selects one of the responses
// based on current gnt/data_gnt
wire [2 : 0] resp0;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data0;
`ifdef MASTER0
assign resp0 = { s_hresp_from_all_slave[ 1 : 0 ],  s_hready_from_all_slave[0]};
assign data0 =  s_hrdata_from_all_slave [`AHB_DATA_WIDTH - 1 : 0];
`else
assign resp0 = 3'b0;
assign data0 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp1;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data1;
`ifdef MASTER1
assign resp1 = { s_hresp_from_all_slave[ 2 * 2 - 1 : 2 ], s_hready_from_all_slave[1]};
assign data1 =  s_hrdata_from_all_slave [2 * `AHB_DATA_WIDTH - 1 : `AHB_DATA_WIDTH];
`else
assign resp1 = 3'b0;
assign data1 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp2;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data2;
`ifdef MASTER2
assign resp2 = { s_hresp_from_all_slave[ 3 * 2 - 1 : 2 * 2 ], s_hready_from_all_slave[2]};
assign data2 =  s_hrdata_from_all_slave [3 * `AHB_DATA_WIDTH - 1 : 2 * `AHB_DATA_WIDTH];
`else
assign resp2 = 3'b0;
assign data2 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp3;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data3;
`ifdef MASTER3
assign resp3 = { s_hresp_from_all_slave[ 4 * 2 - 1 : 3 * 2 ], s_hready_from_all_slave[3]};
assign data3 =  s_hrdata_from_all_slave [4 * `AHB_DATA_WIDTH - 1 : 3 * `AHB_DATA_WIDTH];
`else
assign resp3 = 3'b0;
assign data3 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp4;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data4;
`ifdef MASTER4
assign resp4 = { s_hresp_from_all_slave[ 5 * 2 - 1 : 4 * 2 ], s_hready_from_all_slave[4]};
assign data4 =  s_hrdata_from_all_slave [5 * `AHB_DATA_WIDTH - 1 : 4 * `AHB_DATA_WIDTH];
`else
assign resp4 = 3'b0;
assign data4 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp5;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data5;
`ifdef MASTER5
assign resp5 = { s_hresp_from_all_slave[ 6 * 2 - 1 : 5 * 2 ], s_hready_from_all_slave[5]};
assign data5 =  s_hrdata_from_all_slave [6 * `AHB_DATA_WIDTH - 1 : 5 * `AHB_DATA_WIDTH];
`else
assign resp5 = 3'b0;
assign data5 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp6;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data6;
`ifdef MASTER6
assign resp6 = { s_hresp_from_all_slave[ 7 * 2 - 1 : 6 * 2 ], s_hready_from_all_slave[6]};
assign data6 =  s_hrdata_from_all_slave [7 * `AHB_DATA_WIDTH - 1 : 6 * `AHB_DATA_WIDTH];
`else
assign resp6 = 3'b0;
assign data6 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp7;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data7;
`ifdef MASTER7
assign resp7 = { s_hresp_from_all_slave[ 8 * 2 - 1 : 7 * 2 ], s_hready_from_all_slave[7]};
assign data7 =  s_hrdata_from_all_slave [8 * `AHB_DATA_WIDTH - 1 : 7 * `AHB_DATA_WIDTH];
`else
assign resp7 = 3'b0;
assign data7 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp8;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data8;
`ifdef MASTER8
assign resp8 = { s_hresp_from_all_slave[ 9 * 2 - 1 : 8 * 2 ], s_hready_from_all_slave[8]};
assign data8 =  s_hrdata_from_all_slave [9 * `AHB_DATA_WIDTH - 1 : 8 * `AHB_DATA_WIDTH];
`else
assign resp8 = 3'b0;
assign data8 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp9;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data9;
`ifdef MASTER9
assign resp9 = { s_hresp_from_all_slave[ 10 * 2 - 1 : 9 * 2 ], s_hready_from_all_slave[9]};
assign data9 =  s_hrdata_from_all_slave [10 * `AHB_DATA_WIDTH - 1 : 9 * `AHB_DATA_WIDTH];
`else
assign resp9 = 3'b0;
assign data9 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp10;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data10;
`ifdef MASTER10
assign resp10 = { s_hresp_from_all_slave[ 11 * 2 - 1 : 10 * 2 ], s_hready_from_all_slave[10]};
assign data10 =  s_hrdata_from_all_slave [11 * `AHB_DATA_WIDTH - 1 : 10 * `AHB_DATA_WIDTH];
`else
assign resp10 = 3'b0;
assign data10 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp11;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data11;
`ifdef MASTER11
assign resp11 = { s_hresp_from_all_slave[ 12 * 2 - 1 : 11 * 2 ], s_hready_from_all_slave[11]};
assign data11 =  s_hrdata_from_all_slave [12 * `AHB_DATA_WIDTH - 1 : 11 * `AHB_DATA_WIDTH];
`else
assign resp11 = 3'b0;
assign data11 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp12;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data12;
`ifdef MASTER12
assign resp12 = { s_hresp_from_all_slave[ 13 * 2 - 1 : 12 * 2 ], s_hready_from_all_slave[12]};
assign data12 =  s_hrdata_from_all_slave [13 * `AHB_DATA_WIDTH - 1 : 12 * `AHB_DATA_WIDTH];
`else
assign resp12 = 3'b0;
assign data12 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp13;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data13;
`ifdef MASTER13
assign resp13 = { s_hresp_from_all_slave[ 14 * 2 - 1 : 13 * 2 ], s_hready_from_all_slave[13]};
assign data13 =  s_hrdata_from_all_slave [14 * `AHB_DATA_WIDTH - 1 : 13 * `AHB_DATA_WIDTH];
`else
assign resp13 = 3'b0;
assign data13 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp14;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data14;
`ifdef MASTER14
assign resp14 = { s_hresp_from_all_slave[ 15 * 2 - 1 : 14 * 2 ], s_hready_from_all_slave[14]};
assign data14 =  s_hrdata_from_all_slave [15 * `AHB_DATA_WIDTH - 1 : 14 * `AHB_DATA_WIDTH];
`else
assign resp14 = 3'b0;
assign data14 =  `AHB_DATA_WIDTH'b0;
`endif


wire [2 : 0] resp15;
wire [`AHB_DATA_WIDTH - 1 : 0 ] data15;
`ifdef MASTER15
assign resp15 = { s_hresp_from_all_slave[ 16 * 2 - 1 : 15 * 2 ], s_hready_from_all_slave[15]};
assign data15 =  s_hrdata_from_all_slave [16 * `AHB_DATA_WIDTH - 1 : 15 * `AHB_DATA_WIDTH];
`else
assign resp15 = 3'b0;
assign data15 =  `AHB_DATA_WIDTH'b0;
`endif



// Output of mux is assigned to signals which are given to transaction 
// originating AHB master
assign hready_out_from_slave = mux_out[0];
assign hresp_from_slave = mux_out[2:1];
assign hrdata_out = data_mux_out;




req_register   i_req_reg (

    // input ports 
    
    .hclk(hclk),   // i/p
    .hresetn(hresetn),   
    .hsel(hsel),
    .haddr(haddr),
    .htrans(htrans),
    .hwrite(hwrite),
    .hsize(hsize),
    .hburst(hburst),
    .hprot(hprot),
    .hready(hready),
    .gnt(gnt),   // From master interface
    .hready_out_from_slave(hready_out_from_slave),  // From master interface
    .hresp_from_slave(hresp_from_slave),  // From master interface
   

   // output ports
   .haddr_out(haddr_int),
   .htrans_out(htrans_int),
   .hwrite_out(hwrite_int),
   .hsize_out(hsize_int),
   .hburst_out(hburst_int),
   .hprot_out(hprot_int),
   .hresp_out(hresp_out),
   .hready_out(hready_out),
   .data_gnt(data_gnt),
   .master_sel(req)

);



// Configurable mux instance. It slects HRESP/HREADY from one of the 
// master interface
// 16 is the number of inputs
// 3 is width of each of the inputs

config_mux #(16, 3) i_resp_config_mux (

   // input ports
   .input0(resp0),
   .input1(resp1),
   .input2(resp2),
   .input3(resp3),
   .input4(resp4),
   .input5(resp5),
   .input6(resp6),
   .input7(resp7),
   .input8(resp8),
   .input9(resp9),
   .input10(resp10),
   .input11(resp11),
   .input12(resp12),
   .input13(resp13),
   .input14(resp14),
   .input15(resp15),
   .select({{(16 - `NUM_OF_MASTERS){1'b0}}, ( gnt | data_gnt) }), 

   // output ports
   .out(mux_out)

);


// Configurable mux instance. It slects HRDATA from one of the 
// master interface
// 16 is the number of inputs
config_mux #(16, `AHB_DATA_WIDTH) i_rdata_config_mux (

   // input ports
   .input0(data0),
   .input1(data1),
   .input2(data2),
   .input3(data3),
   .input4(data4),
   .input5(data5),
   .input6(data6),
   .input7(data7),
   .input8(data8),
   .input9(data9),
   .input10(data10),
   .input11(data11),
   .input12(data12),
   .input13(data13),
   .input14(data14),
   .input15(data15),
   .select({{(16 - `NUM_OF_MASTERS){1'b0}}, data_gnt}), 

   // output ports
   .out(data_mux_out)

);


endmodule
