//File name   : uart0_veneer.v
//Title       : 
//Created     : 1999
//Description : 
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

`include "uart_defines.v"

module uart0_veneer (
   // Inputs
   n_p_reset,          
   pclk,              
   n_p_reset_SRPG,          
   pclk_SRPG,              
   uart_clk,             
   psel,              
   penable,           
   pwrite,           
   paddr,            
   pwdata,          
   byte_sel,          
   ua_rxd,
   ua_ncts,           
   scan_en,       
   scan_in_1,      
   scan_in_2,      
  
   // Outputs
   prdata,          
   ua_int,            
   ua_txd, 
   ua_nrts, 
   ua_uclken,            

   scan_out_1,           
   scan_out_2           
   
);

parameter APB_WIDTH         =  `UA_APB_WIDTH,          // Width of APB bus
          DEF_BAUD          =  `UA_DEF_BAUD_RATE,      // Default baud rate
          RX_FIFO_DEPTH     =  `UA_RX_FIFO_DEPTH,      // Receiver fifo depth
          TX_FIFO_DEPTH     =  `UA_TX_FIFO_DEPTH,      // Transmitter fifo depth
          RX_POINTER_WIDTH  =  `UA_RX_POINTER_WIDTH,   // Rx fifo pointer width
          TX_POINTER_WIDTH  =  `UA_TX_POINTER_WIDTH;   // Tx fifo pointer width


   // I/O Signal Declarations

   // Inputs
   input                n_p_reset;    // APB async reset active low
   input                pclk;         // APB clock
   input                n_p_reset_SRPG;    // APB async reset active low
   input                pclk_SRPG;         // APB clock
   input                uart_clk;     // External mux of pclk or user supplied
   input                psel;         // UART peripheral select 
   input                penable;      // UART peripheral enable 
   input                pwrite;       // APB write not read control 
   input [6:0]              paddr;    // APB address bus
   input [(APB_WIDTH-1):0]  pwdata;   // Written data from APB databus
   input                byte_sel;     // byte select from bridge
   input                ua_rxd;       // UART receiver serial input pin
   input                ua_ncts;      // Clear-To-Send flow control
   input                scan_en;      // Enable for scan - unconnected
   input                scan_in_1;    // Scan chain input port 
   input                scan_in_2;    // Scan chain input port 

   // Output
   output [(APB_WIDTH-1):0] prdata;   // Data passed to APB databus
   output               ua_int;       // UART module interrupt 
   output               ua_txd;       // UART transmitter serial output 
   output               ua_nrts;      // Request-To-Send flow control
   output               ua_uclken;    // Soft control of clock
   output               scan_out_1;   // Scan chain output port
   output               scan_out_2;   // Scan chain output port

//##############################################################################
// if the UART0 is NOT black boxed 
//##############################################################################
`ifndef FV_KIT_BLACK_BOX_UART0 

uart i_uart0(
       // Inputs
   .n_p_reset(n_p_reset),
   .pclk(pclk),
   .n_p_reset_SRPG(n_p_reset_SRPG),
   .pclk_SRPG(pclk_SRPG),
   .uart_clk(uart_clk),
   .psel(psel),
   .penable(penable),
   .pwrite(pwrite),
   .paddr(paddr),
   .pwdata(pwdata),
   .byte_sel(byte_sel),
   .ua_rxd(ua_rxd),
   .ua_ncts(ua_ncts),
   .scan_en(scan_en),
   .scan_in_1(),
   .scan_in_2(),

   	// Outputs
   .prdata(prdata),
   .ua_int(ua_int),
   .ua_txd(ua_txd),
   .ua_nrts(ua_nrts),
   .ua_uclken(ua_uclken),
   .scan_out_1(scan_out_1),
   .scan_out_2(scan_out_2)
);

`else 
//##############################################################################
// if the UART0 is black boxed 
//##############################################################################

   // I/O Signal Declarations

   // Inputs
   wire                 n_p_reset;    // APB async reset active low
   wire                 pclk;         // APB clock
   wire                 n_p_reset_SRPG;    // APB async reset active low
   wire                 pclk_SRPG;         // APB clock
   wire                 uart_clk;     // External mux of pclk or user supplied
   wire                 psel;         // UART peripheral select 
   wire                 penable;      // UART peripheral enable 
   wire                 pwrite;       // APB write not read control 
   wire  [6:0]              paddr;    // APB address bus
   wire  [(APB_WIDTH-1):0]  pwdata;   // Written data from APB databus
   wire                 byte_sel;     // byte select from bridge
   wire                 ua_rxd;       // UART receiver serial wire  pin
   wire                 ua_ncts;      // Clear-To-Send flow control
   wire                 scan_en;      // Enable for scan - unconnected
   wire                 scan_in_1;    // Scan chain wire  port 
   wire                 scan_in_2;    // Scan chain wire  port 

   // Output
   reg    [(APB_WIDTH-1):0] prdata;   // Data passed to APB databus
   reg                  ua_int =0;       // UART module interrupt 
   reg                  ua_txd;       // UART transmitter serial reg    
   reg                  ua_nrts;      // Request-To-Send flow control
   reg                  ua_uclken;    // Soft control of clock
   reg                  scan_out_1;   // Scan chain reg    port
   reg                  scan_out_2;   // Scan chain reg    port


`endif
//##############################################################################
// black boxed defines 
//##############################################################################

endmodule
