//File name   : spi_veneer.v
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

`include "spi_defines.v" 

module spi_veneer (
// inputs for scan test
    scan_en,
    scan_in_1,
    scan_in_2,
// inputs to APB block
    n_p_reset,    
    pclk,
    psel,
    penable,
    pwrite,
    paddr,
    pwdata,
// inputs to SPI 
    si,
    n_ss_in,
    mi,
    ext_clk,
    sclk_in,
    slave_in_clk,

// outputs from APB
    prdata,       
    interrupt,
// outputs for scan test
    scan_out_1,     
    scan_out_2,     
// outputs from SPI
    so,           
    mo,           
    sclk_out,     
    n_ss_out,     
    n_so_en,      
    n_mo_en,      
    n_sclk_en,    
    n_ss_en,      
    slave_out_clk 
);

// define parameters
// change using defaparam statements
parameter CHAINS = `SPI_CHAINS;         // number of scan chains
parameter APB_ADDR = `SPI_APB_ADDR;   // size of APB address bus
parameter APB_RDATA = `SPI_APB_RDATA;   // size of APB read data bus
parameter APB_WDATA = `SPI_APB_WDATA;   // size of APB write data bus
parameter DELAY_SIZE = `SPI_DELAY_SIZE; // size of delay REGISTER sub-division
parameter D_SIZE = `SPI_D_SIZE;       // size of datasize word
parameter P_SIZE = `SPI_P_SIZE;       // number of peripheral select lines
parameter BR = `BRATE;                // baud rate word input to control block
parameter W_SIZE = `FF_W;             // size of FIFO word (8, 16, 24 or 31)
parameter SIC = `SPI_SIC_REG;         // size of Slave IDle count register

// declare SPI I/O
 input scan_en;                   // scan enable
 input scan_in_1;                   // scan chain inputs(pclk)
 input scan_in_2;                   // scan chain inputs(slave_in_clk)

// inputs to APB block
 input    n_p_reset;              // active low APB reset
 input    pclk;                   // APB bus clock
 input    psel;                   // APB peripheral select
 input    penable;                // enable active H on the 2nd APB cycle
 input    pwrite;                 // when high write; low read
 input [APB_ADDR-1:0]    paddr;   // APB address bus
 input [APB_WDATA-1:0]   pwdata;  // APB unidirectional write data bus

// inputs to SPI 
 input    si;                     // data input to slave
 input    n_ss_in;                // select input to slave
 input    mi;                     // data input to master
 input    ext_clk;                // external clock
 input    sclk_in;                // clock input to slave
 input    slave_in_clk;           // modified slave clock input

// outputs from APB block
 output [APB_RDATA-1:0] prdata;   // APB unidirectional read data bus
 output    interrupt;             // interrupt request

// outputs from test block
 output   scan_out_1;    // scan chain outputs(pclk)
 output   scan_out_2;    // scan chain outputs(slave_in_clk)

// outputs from SPI
 output    so;                    // data output from slave
 output    mo;                    // data output from master
 output    sclk_out;              // clock output from master
 output [P_SIZE-1:0] n_ss_out;    // peripheral select lines from master
 output    n_so_en;               // out enable for slave data
 output    n_mo_en;               // out enable for master data
 output    n_sclk_en;             // out enable for master clock
 output    n_ss_en;               // out enable for master peripheral lines
 output    slave_out_clk;         // modified slave clock output
//*************************************************

//##############################################################################
// if the SPI is NOT black boxed 
//##############################################################################
`ifndef FV_KIT_BLACK_BOX_SPI 

spi i_spi (
   //inputs
   // inputs for scan test
   .scan_en(scan_en),
   .scan_in_1(),
   .scan_in_2(),
   // inputs to APB block
   .n_p_reset(n_p_reset),
   .pclk(pclk),
   .psel(psel),
   .penable(penable),
   .pwrite(pwrite),
   .paddr(paddr),
   .pwdata(pwdata),
   // inputs to SPI
   .si(si),
   .n_ss_in(n_ss_in),
   .mi(mi),
   .ext_clk(ext_clk),
   .sclk_in(sclk_in),
   .slave_in_clk(slave_out_clk),
   //outputs
   // outputs from APB
   .prdata(prdata),
   .interrupt(interrupt),
   // outputs for scan test
   .scan_out_1(),
   .scan_out_2(),
   // outputs from SPI
   .so(so),
   .mo(mo),
   .sclk_out(sclk_out),
   .n_ss_out(n_ss_out),
   .n_so_en(n_so_en),
   .n_mo_en(n_mo_en),
   .n_sclk_en(n_sclk_en),
   .n_ss_en(n_ss_en),
   .slave_out_clk(slave_out_clk)
);


`else 
//##############################################################################
// if the <module> is black boxed 
//##############################################################################

// declare SPI I/O
 wire  scan_en;                   // scan enable
 wire  scan_in_1;                   // scan chain inputs(pclk)
 wire  scan_in_2;                   // scan chain inputs(slave_in_clk)

// inputs to APB block
 wire     n_p_reset;              // active low APB reset
 wire     pclk;                   // APB bus clock
 wire     psel;                   // APB peripheral select
 wire     penable;                // enable active H on the 2nd APB cycle
 wire     pwrite;                 // when high write; low read
 wire  [APB_ADDR-1:0]    paddr;   // APB address bus
 wire  [APB_WDATA-1:0]   pwdata;  // APB unidirectional write data bus

// inputs to SPI 
 wire     si;                     // data wire  to slave
 wire     n_ss_in;                // select wire  to slave
 wire     mi;                     // data wire  to master
 wire     ext_clk;                // external clock
 wire     sclk_in;                // clock wire  to slave
 wire     slave_in_clk;           // modified slave clock input

// outputs from APB block
 reg    [APB_RDATA-1:0] prdata;   // APB unidirectional read data bus
 reg       interrupt =0;             // interrupt request

// outputs from test block
 reg      scan_out_1;    // scan chain outputs(pclk)
 reg      scan_out_2;    // scan chain outputs(slave_in_clk)

// outputs from SPI
 reg       so;                    // data reg    from slave
 reg       mo;                    // data reg    from master
 reg       sclk_out;              // clock reg    from master
 reg    [P_SIZE-1:0] n_ss_out;    // peripheral select lines from master
 reg       n_so_en;               // out enable for slave data
 reg       n_mo_en;               // out enable for master data
 reg       n_sclk_en;             // out enable for master clock
 reg       n_ss_en;               // out enable for master peripheral lines
 reg       slave_out_clk;         // modified slave clock output
//*************************************************


`endif
//##############################################################################
// black boxed defines 
//##############################################################################

endmodule
