//File name   : master_if.v
//Title       : 
//Created     : 1999
//Description : This module selects the transaction attributes of the selected 
//              Slave interface and puts it on the external master interface bus.
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

module master_if (

  // input ports
  hclk,
  hresetn,
  s_haddr,    // This HADDR combined from all the Slave interfaces
  s_htrans,   // This HTRANS combined from all the Slave interfaces
  s_hwrite,   // This HWRITE combined from all the Slave interfaces
  s_hsize,    // This HSIZE combined from all the Slave interfaces
  s_hburst,   // This HBURST combined from all the Slave interfaces
  s_hprot,    // This HPROT combined from all the Slave interfaces
  s_hready,   // This HREADY combined from all the Slave interfaces
  s_req,      // This Request combined from all the Slave interfaces
  s_hwdata,   // This HWDATA combined from all the Slave interfaces
  
  hready_in_from_slave, // This is HREADYOUT input from target slave
  hresp_in_from_slave,  // This is HRESP input from target slave

  // output ports
  m_hsel,     // HSEL on master interface
  m_haddr,    // HADDR on master interface
  m_htrans,   // HTRANS on master interface
  m_hwrite,   // HWRITE on master interface
  m_hsize,    // HSIZE on master interface
  m_hburst,   // HBURST on master interface
  m_hprot,    // HPROT on master interface
  m_hready,   // HREADYMUX on master interface
  m_hwdata,   // HWDATA on master interface
  
  hready_out_from_slave, // HREADYOUT input from target slave
  hresp_from_slave,      // HRESP input from target slave
  gnt                    // Access grant to Slave interfaces

);

`include "bm_defs.v"

input hclk;
input hresetn;
input [`NUM_OF_SLAVES * `AHB_ADDR_WIDTH - 1 : 0] s_haddr;
input [`NUM_OF_SLAVES * 2 - 1 :0] s_htrans;
input [`NUM_OF_SLAVES - 1 : 0] s_hwrite;
input [`NUM_OF_SLAVES * 3 - 1 : 0] s_hsize;
input [`NUM_OF_SLAVES * 3 - 1 : 0] s_hburst;
input [`NUM_OF_SLAVES * 4 - 1 : 0] s_hprot;
input [`NUM_OF_SLAVES - 1 : 0] s_hready;
input [`NUM_OF_SLAVES - 1 : 0] s_req;
input [`NUM_OF_SLAVES * `AHB_DATA_WIDTH - 1 : 0] s_hwdata;

input hready_in_from_slave;
input [1 : 0] hresp_in_from_slave;


output m_hsel;
output [`AHB_ADDR_WIDTH - 1 : 0] m_haddr;
output [1 :0] m_htrans;
output  m_hwrite;
output [2 : 0] m_hsize;
output [2 : 0] m_hburst;
output [3 : 0] m_hprot;
output  m_hready;
output [`AHB_DATA_WIDTH - 1 : 0] m_hwdata;

output hready_out_from_slave;
output [1 : 0] hresp_from_slave;
output [`NUM_OF_SLAVES - 1 : 0] gnt;


wire m_hsel;
wire [`AHB_ADDR_WIDTH - 1 : 0] m_haddr;
wire [1 :0] m_htrans;
wire  m_hwrite;
wire [2 : 0] m_hsize;
wire [2 : 0] m_hburst;
wire [3 : 0] m_hprot;
wire  m_hready;
wire [`AHB_DATA_WIDTH - 1 : 0] m_hwdata;

wire hready_out_from_slave;
wire [1 : 0] hresp_from_slave;
wire [`NUM_OF_SLAVES - 1 : 0] gnt;

reg [`NUM_OF_SLAVES - 1 : 0] data_gnt;


wire [45 : 0] mux_out;
wire [`AHB_DATA_WIDTH - 1 : 0] data_mux_out;


assign hready_out_from_slave = hready_in_from_slave;
assign hresp_from_slave = hresp_in_from_slave;


assign m_hsel = |gnt;

// Output of mux is seperated into their respective AHB signal
assign   m_haddr  = mux_out[45:14];
assign   m_htrans = mux_out[13:12];
assign   m_hwrite = mux_out[11];
assign   m_hsize  = mux_out[10:8];
assign   m_hburst = mux_out[7:5];
assign   m_hprot  = mux_out[4:1];

// If the target slave is engaged in transaction loop back the incoming
// HREADYOUT from slave else maintain HREADYMUX high
assign m_hready = (m_hsel || (|data_gnt) ) ? hready_in_from_slave : 1'b1;

assign m_hwdata = data_mux_out;



/* 
   Transaction attributes from various slaves is concatenated into 
   respective "trx" signal.  "trx" signals are given to mux to select 
   one of the transactions based on current grant.

   Bits order in tr signals from LSB
   hready - 1 bit
   h_prot - 4 bits
   hburst - 3 bits
   hsize - 3 bits
   hwrite - 1 bit
   htrans -  2bits
   haddr  - 32 bits

 Total - 46 bits

*/


wire [45 : 0] tr0;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata0;
`ifdef SLAVE0
assign tr0 = {s_haddr[`AHB_ADDR_WIDTH - 1 : 0], s_htrans[1:0], s_hwrite[0], 
              s_hsize[2:0], s_hburst[2:0], s_hprot[3:0], s_hready[0]};
assign s_hwdata0 = s_hwdata[`AHB_DATA_WIDTH - 1 : 0];
`else
assign tr0 = 46'b0;
assign s_hwdata0 = `AHB_DATA_WIDTH'b0;
`endif

wire [45 : 0] tr1;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata1;
`ifdef SLAVE1
assign tr1 = {s_haddr[2 * `AHB_ADDR_WIDTH - 1 : `AHB_ADDR_WIDTH], 
              s_htrans[2 * 2 - 1:2], 
              s_hwrite[1], 
              s_hsize[2 * 3 - 1:3], 
              s_hburst[2 * 3 - 1:3], 
              s_hprot[2 * 4 - 1:4], 
              s_hready[1]};
assign s_hwdata1 = s_hwdata[2 * `AHB_DATA_WIDTH - 1 : `AHB_DATA_WIDTH];
`else
assign tr1 = 46'b0;
assign s_hwdata1 = `AHB_DATA_WIDTH'b0;
`endif



wire [45 : 0] tr2;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata2;
`ifdef SLAVE2
assign tr2 = {s_haddr[3 * `AHB_ADDR_WIDTH - 1 : 2 * `AHB_ADDR_WIDTH], 
              s_htrans[3 * 2 - 1 : 2 * 2], 
              s_hwrite[2], 
              s_hsize[3 * 3 - 1: 2 * 3], 
              s_hburst[3 * 3 - 1 : 2 * 3], 
              s_hprot[3 * 4 - 1: 2 * 4], 
              s_hready[2]};
assign s_hwdata2 = s_hwdata[3 * `AHB_DATA_WIDTH - 1 : 2 * `AHB_DATA_WIDTH];
`else
assign tr2 = 46'b0;
assign s_hwdata2 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr3;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata3;
`ifdef SLAVE3
assign tr3 = {s_haddr[4 * `AHB_ADDR_WIDTH - 1 : 3 * `AHB_ADDR_WIDTH], 
              s_htrans[4 * 2 - 1 : 3 * 2], 
              s_hwrite[3], 
              s_hsize[4 * 3 - 1: 3 * 3], 
              s_hburst[4 * 3 - 1 : 3 * 3], 
              s_hprot[4 * 4 - 1: 3 * 4], 
              s_hready[3]};
assign s_hwdata3 = s_hwdata[4 * `AHB_DATA_WIDTH - 1 : 3 * `AHB_DATA_WIDTH];
`else
assign tr3 = 46'b0;
assign s_hwdata3 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr4;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata4;
`ifdef SLAVE4
assign tr4 = {s_haddr[5 * `AHB_ADDR_WIDTH - 1 : 4 * `AHB_ADDR_WIDTH], 
              s_htrans[5 * 2 - 1 : 4 * 2], 
              s_hwrite[4], 
              s_hsize[5 * 3 - 1: 4 * 3], 
              s_hburst[5 * 3 - 1 : 4 * 3], 
              s_hprot[5 * 4 - 1: 4 * 4], 
              s_hready[4]};
assign s_hwdata4 = s_hwdata[5 * `AHB_DATA_WIDTH - 1 : 4 * `AHB_DATA_WIDTH];
`else
assign tr4 = 46'b0;
assign s_hwdata4 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr5;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata5;
`ifdef SLAVE5
assign tr5 = {s_haddr[6 * `AHB_ADDR_WIDTH - 1 : 5 * `AHB_ADDR_WIDTH], 
              s_htrans[6 * 2 - 1 : 5 * 2], 
              s_hwrite[5], 
              s_hsize[6 * 3 - 1: 5 * 3], 
              s_hburst[6 * 3 - 1 : 5 * 3], 
              s_hprot[6 * 4 - 1: 5 * 4], 
              s_hready[5]};
assign s_hwdata5 = s_hwdata[6 * `AHB_DATA_WIDTH - 1 : 5 * `AHB_DATA_WIDTH];
`else
assign tr5 = 46'b0;
assign s_hwdata5 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr6;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata6;
`ifdef SLAVE6
assign tr6 = {s_haddr[7 * `AHB_ADDR_WIDTH - 1 : 6 * `AHB_ADDR_WIDTH], 
              s_htrans[7 * 2 - 1 : 6 * 2], 
              s_hwrite[6], 
              s_hsize[7 * 3 - 1: 6 * 3], 
              s_hburst[7 * 3 - 1 : 6 * 3], 
              s_hprot[7 * 4 - 1: 6 * 4], 
              s_hready[6]};
assign s_hwdata6 = s_hwdata[7 * `AHB_DATA_WIDTH - 1 : 6 * `AHB_DATA_WIDTH];
`else
assign tr6 = 46'b0;
assign s_hwdata6 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr7;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata7;
`ifdef SLAVE7
assign tr7 = {s_haddr[8 * `AHB_ADDR_WIDTH - 1 : 7 * `AHB_ADDR_WIDTH], 
              s_htrans[8 * 2 - 1 : 7 * 2], 
              s_hwrite[7], 
              s_hsize[8 * 3 - 1: 7 * 3], 
              s_hburst[8 * 3 - 1 : 7 * 3], 
              s_hprot[8 * 4 - 1: 7 * 4], 
              s_hready[7]};
assign s_hwdata7 = s_hwdata[8 * `AHB_DATA_WIDTH - 1 : 7 * `AHB_DATA_WIDTH];
`else
assign tr7 = 46'b0;
assign s_hwdata7 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr8;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata8;
`ifdef SLAVE8
assign tr8 = {s_haddr[9 * `AHB_ADDR_WIDTH - 1 : 8 * `AHB_ADDR_WIDTH], 
              s_htrans[9 * 2 - 1 : 8 * 2], 
              s_hwrite[8], 
              s_hsize[9 * 3 - 1: 8 * 3], 
              s_hburst[9 * 3 - 1 : 8 * 3], 
              s_hprot[9 * 4 - 1: 8 * 4], 
              s_hready[8]};
assign s_hwdata8 = s_hwdata[9 * `AHB_DATA_WIDTH - 1 : 8 * `AHB_DATA_WIDTH];
`else
assign tr8 = 46'b0;
assign s_hwdata8 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr9;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata9;
`ifdef SLAVE9
assign tr9 = {s_haddr[10 * `AHB_ADDR_WIDTH - 1 : 9 * `AHB_ADDR_WIDTH], 
              s_htrans[10 * 2 - 1 : 9 * 2], 
              s_hwrite[9], 
              s_hsize[10 * 3 - 1: 9 * 3], 
              s_hburst[10 * 3 - 1 : 9 * 3], 
              s_hprot[10 * 4 - 1: 9 * 4], 
              s_hready[9]};
assign s_hwdata9 = s_hwdata[10 * `AHB_DATA_WIDTH - 1 : 9 * `AHB_DATA_WIDTH];
`else
assign tr9 = 46'b0;
assign s_hwdata9 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr10;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata10;
`ifdef SLAVE10
assign tr10 = {s_haddr[11 * `AHB_ADDR_WIDTH - 1 : 10 * `AHB_ADDR_WIDTH], 
               s_htrans[11 * 2 - 1 : 10 * 2], 
               s_hwrite[10], 
               s_hsize[11 * 3 - 1: 10 * 3], 
               s_hburst[11 * 3 - 1 : 10 * 3], 
               s_hprot[11 * 4 - 1: 10 * 4], 
               s_hready[10]};
assign s_hwdata10 = s_hwdata[11 * `AHB_DATA_WIDTH - 1 : 10 * `AHB_DATA_WIDTH];
`else
assign tr10 = 46'b0;
assign s_hwdata10 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr11;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata11;
`ifdef SLAVE11
assign tr11 = {s_haddr[12 * `AHB_ADDR_WIDTH - 1 : 11 * `AHB_ADDR_WIDTH], 
               s_htrans[12 * 2 - 1 : 11 * 2], 
               s_hwrite[11], 
               s_hsize[12 * 3 - 1: 11 * 3], 
               s_hburst[12 * 3 - 1 : 11 * 3], 
               s_hprot[12 * 4 - 1: 11 * 4], 
               s_hready[11]};
assign s_hwdata11 = s_hwdata[12 * `AHB_DATA_WIDTH - 1 : 11 * `AHB_DATA_WIDTH];
`else
assign tr11 = 46'b0;
assign s_hwdata11 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr12;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata12;
`ifdef SLAVE12
assign tr12 = {s_haddr[13 * `AHB_ADDR_WIDTH - 1 : 12 * `AHB_ADDR_WIDTH], 
               s_htrans[13 * 2 - 1 : 12 * 2], 
               s_hwrite[12], 
               s_hsize[13 * 3 - 1: 12 * 3], 
               s_hburst[13 * 3 - 1 : 12 * 3], 
               s_hprot[13 * 4 - 1: 12 * 4], 
               s_hready[12]};
assign s_hwdata12 = s_hwdata[13 * `AHB_DATA_WIDTH - 1 : 12 * `AHB_DATA_WIDTH];
`else
assign tr12 = 46'b0;
assign s_hwdata12 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr13;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata13;
`ifdef SLAVE13
assign tr13 = {s_haddr[14 * `AHB_ADDR_WIDTH - 1 : 13 * `AHB_ADDR_WIDTH], 
               s_htrans[14 * 2 - 1 : 13 * 2], 
               s_hwrite[13], 
               s_hsize[14 * 3 - 1: 13 * 3], 
               s_hburst[14 * 3 - 1 : 13 * 3], 
               s_hprot[14 * 4 - 1: 13 * 4], 
               s_hready[13]};
assign s_hwdata13 = s_hwdata[14 * `AHB_DATA_WIDTH - 1 : 13 * `AHB_DATA_WIDTH];
`else
assign tr13 = 46'b0;
assign s_hwdata13 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr14;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata14;
`ifdef SLAVE14
assign tr14 = {s_haddr[15 * `AHB_ADDR_WIDTH - 1 : 14 * `AHB_ADDR_WIDTH], 
               s_htrans[15 * 2 - 1 : 14 * 2], 
               s_hwrite[14], 
               s_hsize[15 * 3 - 1: 14 * 3], 
               s_hburst[15 * 3 - 1 : 14 * 3], 
               s_hprot[15 * 4 - 1: 14 * 4], 
               s_hready[14]};
assign s_hwdata14 = s_hwdata[15 * `AHB_DATA_WIDTH - 1 : 14 * `AHB_DATA_WIDTH];
`else
assign tr14 = 46'b0;
assign s_hwdata14 = `AHB_DATA_WIDTH'b0;
`endif


wire [45 : 0] tr15;
wire [`AHB_DATA_WIDTH - 1 : 0] s_hwdata15;
`ifdef SLAVE15
assign tr15 = {s_haddr[16 * `AHB_ADDR_WIDTH - 1 : 15 * `AHB_ADDR_WIDTH], 
               s_htrans[16 * 2 - 1 : 15 * 2], 
               s_hwrite[15], 
               s_hsize[16 * 3 - 1: 15 * 3], 
               s_hburst[16 * 3 - 1 : 15 * 3], 
               s_hprot[16 * 4 - 1: 15 * 4], 
               s_hready[15]};
assign s_hwdata15 = s_hwdata[16 * `AHB_DATA_WIDTH - 1 : 15 * `AHB_DATA_WIDTH];
`else
assign tr15 = 46'b0;
assign s_hwdata15 = `AHB_DATA_WIDTH'b0;
`endif




// Store the grant during address phase for data phase
// "data_gnt" is used during data phase to select data from appropriate
// slave interface
always @ (posedge hclk or negedge hresetn)
  if (~hresetn)
    data_gnt <= 0;
  else
    if (|gnt && hready_in_from_slave)
       data_gnt <=gnt;


// Arbiter instance
arbiter  i_arbiter (

  // input ports
  .hclk(hclk),
  .hresetn(hresetn),
  .req(s_req),
  .hreadyout(hready_in_from_slave),

  // output ports
  .gnt(gnt)
);


// Configurable Mux instance
// 16 is number of inputs to mux
// 46 is width of each input
// It selects transaction attributes from Slave interfaces based on 
// current grant
config_mux #(16, 46) i_tr_config_mux (

   // input ports
   .input0(tr0),
   .input1(tr1),
   .input2(tr2),
   .input3(tr3),
   .input4(tr4),
   .input5(tr5),
   .input6(tr6),
   .input7(tr7),
   .input8(tr8),
   .input9(tr9),
   .input10(tr10),
   .input11(tr11),
   .input12(tr12),
   .input13(tr13),
   .input14(tr14),
   .input15(tr15),
   .select({{(16 - `NUM_OF_SLAVES){1'b0}}, gnt}),

   // output ports
   .out(mux_out)

);



// Configurable Mux instance
// 16 is number of inputs to mux
// It selects HWDATA from Slave interfaces based on current data_grant
config_mux #(16, `AHB_DATA_WIDTH) i_wdata_config_mux(

   // input ports
   .input0(s_hwdata0),
   .input1(s_hwdata1),
   .input2(s_hwdata2),
   .input3(s_hwdata3),
   .input4(s_hwdata4),
   .input5(s_hwdata5),
   .input6(s_hwdata6),
   .input7(s_hwdata7),
   .input8(s_hwdata8),
   .input9(s_hwdata9),
   .input10(s_hwdata10),
   .input11(s_hwdata11),
   .input12(s_hwdata12),
   .input13(s_hwdata13),
   .input14(s_hwdata14),
   .input15(s_hwdata15),
   .select({{(16 - `NUM_OF_SLAVES){1'b0}}, data_gnt}),

   // output ports
   .out(data_mux_out)

);



endmodule
