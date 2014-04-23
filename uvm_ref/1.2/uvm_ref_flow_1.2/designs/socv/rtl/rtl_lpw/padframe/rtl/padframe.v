//File name   : padframe.v
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

module padframe(
    //inputs
      ua_NCTS_pad,
      ua_RXDA_pad,
      ua_txd,
      ua_NCTS1_pad,
      ua_RXDA1_pad,
      ua_txd1,
      ua_nrts,
      ua_nrts1,

      jtag_NTRST_pad,
      jtag_TCK_pad,
      jtag_TMS_pad,
      jtag_TDI_pad,
      jtag_tdo,
      jtag_oe,
	   shift_en_pad,

   	scan_chain_out_,
      scan_mode_pf,
      MBIST_en_pad,
      MBIST_en,

      gpio_pin_out,
      n_gpio_pin_oe,

      spi_N_ss_in_pad,
      so,
      mo,
      sclk_out,
      n_sclk_en,
      n_so_en, 
      n_mo_en,
      n_ss_en,
      n_ss_out,


      smc_n_be,
      smc_addr,
      smc_n_cs,
      smc_n_we,
      smc_n_wr,
      smc_n_rd,
      smc_data,
      smc_n_ext_oe,

      hiss_rxien,
      hiss_rxqen,
      hiss_clken,
      hissrxip,
      hissrxin,
      hissclkp,
      hissclkn,
      hissrxqp,
      hissrxqn,
      
      vdd_hiss,
      vss_hiss,
      vsub_hiss,
      hiss_biasen,
      hiss_replien,
      hiss_curr,
      hiss_txi,
      hiss_txq,
      hiss_txien,
      hiss_txqen,

      pin_reset_pad,
      pin_32k_pad,
      pin_sysclk_pad,
      pin_12M_pad,

      rf_reset_n,
      rf_en,
      rf_sw,
      
      macb0_col_pad,        
      macb0_crs_pad,       
      macb0_tx_clk_pad,   
      macb0_rxd_pad,     
      macb0_rx_er_pad,  
      macb0_rx_clk_pad,
      macb0_rx_dv_pad,    
      macb_mdio_in_pad,    

      macb0_tx_er,       
      macb0_txd,        
      macb0_tx_en,     
      macb_mdc,            
      macb_mdio_out,       
      macb_mdio_en,        
                           
      macb1_col_pad,        
      macb1_crs_pad,       
      macb1_tx_clk_pad,   
      macb1_rxd_pad,     
      macb1_rx_er_pad,  
      macb1_rx_clk_pad,
      macb1_rx_dv_pad,    

      macb1_tx_er,       
      macb1_txd,        
      macb1_tx_en,     

      macb2_col_pad,        
      macb2_crs_pad,       
      macb2_tx_clk_pad,   
      macb2_rxd_pad,     
      macb2_rx_er_pad,  
      macb2_rx_clk_pad,
      macb2_rx_dv_pad,    

      macb2_tx_er,       
      macb2_txd,        
      macb2_tx_en,     

      macb3_col_pad,        
      macb3_crs_pad,       
      macb3_tx_clk_pad,   
      macb3_rxd_pad,     
      macb3_rx_er_pad,  
      macb3_rx_clk_pad,
      macb3_rx_dv_pad,    

      macb3_tx_er,       
      macb3_txd,        
      macb3_tx_en,     

     //outputs
      pin_reset,
      pin_12M,
      pin_32k,
      pin_sysclk,

      rf_resetn_pad,

      ua_ncts,
      ua_rxd,
      ua_NRTS_pad,
      ua_TXDA_pad,
      ua_ncts1,
      ua_rxd1,
      ua_NRTS_pad1,
      ua_TXDA_pad1,

      scan_chain_in_,
	   shift_en,
      jtag_TDO_pad,
      jtag_tck,
      jtag_tms,
      jtag_tdi,
      jtag_ntrst,

      gpio_pin_in,

      n_ss_in,
      mi,
      si,
      sclk_in,
      spi_N_ss_out_pad,


      SMC_n_be_pad,
      SMC_n_CS_pad,
      SMC_n_we_pad,
      SMC_n_wr_pad,
      SMC_n_rd_pad,
      SMC_addr_pad,
      data_smc,

      hisstxip,
      hisstxin,
      hisstxqp,
      hisstxqn,
      hiss_rxi,
      hiss_rxq,
      hiss_clk,

      rf_en_pad,
      rf_sw_pad,


      macb0_tx_er_pad,
      macb0_txd_pad,    
      macb0_tx_en_pad,
      macb_mdc_pad,     
      macb_mdio_out_pad,
      macb_mdio_en_pad, 

      macb0_col,        
      macb0_crs,        
      macb0_tx_clk,     
      macb0_rxd,        
      macb0_rx_er,      
      macb0_rx_clk,     
      macb0_rx_dv,     
      macb_mdio_in,     

      macb1_tx_er_pad,
      macb1_txd_pad,    
      macb1_tx_en_pad,

      macb1_col,        
      macb1_crs,        
      macb1_tx_clk,     
      macb1_rxd,        
      macb1_rx_er,      
      macb1_rx_clk,     
      macb1_rx_dv,     


      macb2_tx_er_pad,
      macb2_txd_pad,    
      macb2_tx_en_pad,

      macb2_col,        
      macb2_crs,        
      macb2_tx_clk,     
      macb2_rxd,        
      macb2_rx_er,      
      macb2_rx_clk,     
      macb2_rx_dv,     

      macb3_tx_er_pad,
      macb3_txd_pad,    
      macb3_tx_en_pad,

      macb3_col,        
      macb3_crs,        
      macb3_tx_clk,     
      macb3_rxd,        
      macb3_rx_er,      
      macb3_rx_clk,     
      macb3_rx_dv,     


    //inout
      GPIO_pad,

      spi_SIMO_pad,
      spi_SOMI_pad,
      spi_CLK_pad,
      
      SMC_data_pad,
      dp,
      dp_pad,
      dn,
      dn_pad,

      rrefext,
      rrefext_pad
     );



//--------------------------------------------------------------------
parameter P_SIZE = `SPI_SS_NB;       // number of peripheral select lines
//--------------------------------------------------------------------
input shift_en_pad;
input scan_mode_pf;
input ua_NCTS_pad,
      ua_RXDA_pad;
input ua_txd,
      ua_nrts;
input ua_NCTS1_pad,
      ua_RXDA1_pad;
input ua_txd1,
      ua_nrts1;
input jtag_NTRST_pad,
      jtag_TCK_pad,
      jtag_TMS_pad,
      jtag_TDI_pad,
      jtag_tdo,
      jtag_oe;
input [15:0]  gpio_pin_out,
      n_gpio_pin_oe;   
input spi_N_ss_in_pad,
      so,
      n_ss_en,
      mo,
      sclk_out,
      n_sclk_en,
       n_so_en,
       n_mo_en;
input [P_SIZE-1:0] n_ss_out;
input [3:0]  smc_n_be,
       smc_n_we;
input [15:0] smc_addr;
input [31:0] smc_data;
input        smc_n_cs;
input  smc_n_wr,
       smc_n_rd,
       smc_n_ext_oe;
input pin_reset_pad;
input pin_32k_pad;
input pin_sysclk_pad;
input pin_12M_pad;
input rf_reset_n;
input rf_en;
input [3:0] rf_sw;
input hiss_rxien,
       hiss_rxqen,
       hiss_clken,
       hissrxip,
       hissrxin,
       hissclkp,
       hissclkn,
       hissrxqp,
       hissrxqn,
      vdd_hiss,
       vss_hiss,
       vsub_hiss,
       hiss_biasen,
       hiss_replien,
       hiss_curr,
      hiss_txi,
       hiss_txq,
       hiss_txien,
       hiss_txqen;
output hisstxip,
       hisstxin,
       hisstxqp,
       hisstxqn,
      hiss_rxi,
       hiss_rxq,
       hiss_clk;
output shift_en;
output ua_ncts,
      ua_rxd;
output ua_ncts1,
      ua_rxd1;
inout  ua_NRTS_pad,
      ua_TXDA_pad;
inout  ua_NRTS_pad1,
      ua_TXDA_pad1;
output pin_reset;
output pin_32k;
output pin_12M;
output pin_sysclk;
output rf_resetn_pad;
output jtag_TDO_pad,
      jtag_tck,
      jtag_tms,
      jtag_tdi,
      jtag_ntrst;
output [15:0] gpio_pin_in;
output n_ss_in,
      sclk_in,
      mi,
      si;
output [P_SIZE-1:0] spi_N_ss_out_pad;
output [3:0] SMC_n_be_pad,
      SMC_n_we_pad;
output SMC_n_wr_pad,
      SMC_n_rd_pad;
output  SMC_n_CS_pad;
output [15:0] SMC_addr_pad;
output [31:0] data_smc;
output rf_en_pad;
output [3:0] rf_sw_pad;
output [15:0] scan_chain_in_;
input  [15:0] scan_chain_out_;
inout  [15:0] GPIO_pad;
inout  spi_SIMO_pad,
      spi_SOMI_pad,
      spi_CLK_pad;
inout  [31:0] SMC_data_pad;
inout  dp,
       dp_pad;
inout  dn,
       dn_pad;
inout  rrefext,
       rrefext_pad;
input	MBIST_en_pad; 
output	MBIST_en;


input         macb0_col_pad;            // collision detect signal from the PHY
input         macb0_crs_pad;            // carrier sense signal from the PHY
input         macb0_tx_clk_pad;         // transmit clock from the PHY
input   [3:0] macb0_rxd_pad;            // receive data from the PHY
input         macb0_rx_er_pad;          // receive error signal from the PHY
input         macb0_rx_clk_pad;         // receive clock from the PHY
input         macb0_rx_dv_pad;          // receive data valid signal from the PHY
input         macb_mdio_in_pad;        // management data input 

input         macb0_tx_er;         
input  [3:0]  macb0_txd;           
input         macb0_tx_en;         
input         macb_mdc;            
input         macb_mdio_out;       
input         macb_mdio_en;        


input         macb1_col_pad;      
input         macb1_crs_pad;     
input         macb1_tx_clk_pad; 
input   [3:0] macb1_rxd_pad;   
input         macb1_rx_er_pad;
input         macb1_rx_clk_pad;    
input         macb1_rx_dv_pad;  

input         macb1_tx_er;         
input  [3:0]  macb1_txd;           
input         macb1_tx_en;         

input         macb2_col_pad;   
input         macb2_crs_pad;  
input         macb2_tx_clk_pad;    
input   [3:0] macb2_rxd_pad; 
input         macb2_rx_er_pad;   
input         macb2_rx_clk_pad; 
input         macb2_rx_dv_pad; 

input         macb2_tx_er;         
input  [3:0]  macb2_txd;           
input         macb2_tx_en;         

input         macb3_col_pad;  
input         macb3_crs_pad; 
input         macb3_tx_clk_pad;    
input   [3:0] macb3_rxd_pad;       
input         macb3_rx_er_pad;  
input         macb3_rx_clk_pad;    
input         macb3_rx_dv_pad; 

input         macb3_tx_er;         
input  [3:0]  macb3_txd;           
input         macb3_tx_en;         

output        macb0_tx_er_pad;          // transmit error signal to the PHY
output  [3:0] macb0_txd_pad;            // transmit data to the PHY
output        macb0_tx_en_pad;          // transmit enable signal to the PHY
output        macb_mdc_pad;            // management data clock
output        macb_mdio_out_pad;       // management data output
output        macb_mdio_en_pad;        // management data output enable

output        macb0_col;            
output        macb0_crs;           
output        macb0_tx_clk;       
output  [3:0] macb0_rxd;         
output        macb0_rx_er;      
output        macb0_rx_clk;    
output        macb0_rx_dv;    
output        macb_mdio_in;  


output        macb1_tx_er_pad;  
output  [3:0] macb1_txd_pad;   
output        macb1_tx_en_pad;

output        macb1_col;            
output        macb1_crs;           
output        macb1_tx_clk;       
output  [3:0] macb1_rxd;         
output        macb1_rx_er;      
output        macb1_rx_clk;    
output        macb1_rx_dv;    

output        macb2_tx_er_pad;  
output  [3:0] macb2_txd_pad;   
output        macb2_tx_en_pad;

output        macb2_col;            
output        macb2_crs;           
output        macb2_tx_clk;       
output  [3:0] macb2_rxd;         
output        macb2_rx_er;      
output        macb2_rx_clk;    
output        macb2_rx_dv;    

output        macb3_tx_er_pad;  
output  [3:0] macb3_txd_pad;   
output        macb3_tx_en_pad;

output        macb3_col;            
output        macb3_crs;           
output        macb3_tx_clk;       
output  [3:0] macb3_rxd;         
output        macb3_rx_er;      
output        macb3_rx_clk;    
output        macb3_rx_dv;    

genvar i;

//--------------------------------------------------------------------

wire [15:0]  gpio_pin_out_mux;
wire [15:0]  n_gpio_pin_oe_mux;
wire 	n_so_en_mux;  
wire 	n_mo_en_mux;  
wire 	n_sclk_en_mux;
wire 	ua_ncts;
wire 	ua_rxd;
wire 	ua_ncts1;
wire 	ua_rxd1;
wire	si;
wire	so;
wire	sclk_in;
wire	n_ss_in;
wire	scan_chain_in_12;
wire	scan_chain_in_13;
wire	scan_chain_in_14;
wire	scan_chain_in_15;
//--------------------------------------------------------------------

assign scan_chain_in_[0] = ua_ncts;
assign scan_chain_in_[1] = ua_rxd;
assign scan_chain_in_[2] = ua_ncts1;
assign scan_chain_in_[3] = ua_rxd1;
assign scan_chain_in_[4] = 1'b0;
assign scan_chain_in_[5] = 1'b0;
assign scan_chain_in_[6] = 1'b0;
assign scan_chain_in_[7] = 1'b0;
assign scan_chain_in_[8] = si;
assign scan_chain_in_[9] = mi;
assign scan_chain_in_[10] = sclk_in;
assign scan_chain_in_[11] = n_ss_in;
assign scan_chain_in_[12] = scan_chain_in_12;
assign scan_chain_in_[13] = scan_chain_in_13;
assign scan_chain_in_[14] = scan_chain_in_14;
assign scan_chain_in_[15] = scan_chain_in_15;

//MACB input pads
PDIDGZ i_macb0_col(.PAD(macb0_col_pad),.C(macb0_col));
PDIDGZ i_macb1_col(.PAD(macb1_col_pad),.C(macb1_col));
PDIDGZ i_macb2_col(.PAD(macb2_col_pad),.C(macb2_col));
PDIDGZ i_macb3_col(.PAD(macb3_col_pad),.C(macb3_col));

PDIDGZ i_macb0_crs(.PAD(macb0_crs_pad),.C(macb0_crs));
PDIDGZ i_macb1_crs(.PAD(macb1_crs_pad),.C(macb1_crs));
PDIDGZ i_macb2_crs(.PAD(macb2_crs_pad),.C(macb2_crs));
PDIDGZ i_macb3_crs(.PAD(macb3_crs_pad),.C(macb3_crs));

PDIDGZ i_macb0_tx_clk(.PAD(macb0_tx_clk_pad),.C(macb0_tx_clk));
PDIDGZ i_macb1_tx_clk(.PAD(macb1_tx_clk_pad),.C(macb1_tx_clk));
PDIDGZ i_macb2_tx_clk(.PAD(macb2_tx_clk_pad),.C(macb2_tx_clk));
PDIDGZ i_macb3_tx_clk(.PAD(macb3_tx_clk_pad),.C(macb3_tx_clk));

generate
for ( i = 0; i <=3 ; i = i+1)
begin : MACB0_RXD 
PDIDGZ i_macb0_rxd(.PAD(macb0_rxd_pad[i]),.C(macb0_rxd[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin :  MACB1_RXD
PDIDGZ i_macb1_rxd(.PAD(macb1_rxd_pad[i]),.C(macb1_rxd[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin :  MACB2_RXD
PDIDGZ i_macb2_rxd(.PAD(macb2_rxd_pad[i]),.C(macb2_rxd[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin :  MACB3_RXD
PDIDGZ i_macb3_rxd(.PAD(macb3_rxd_pad[i]),.C(macb3_rxd[i]));
end
endgenerate

PDIDGZ i_macb0_rx_er(.PAD(macb0_rx_er_pad),.C(macb0_rx_er));
PDIDGZ i_macb1_rx_er(.PAD(macb1_rx_er_pad),.C(macb1_rx_er));
PDIDGZ i_macb2_rx_er(.PAD(macb2_rx_er_pad),.C(macb2_rx_er));
PDIDGZ i_macb3_rx_er(.PAD(macb3_rx_er_pad),.C(macb3_rx_er));

PDIDGZ i_macb0_rx_clk(.PAD(macb0_rx_clk_pad),.C(macb0_rx_clk));
PDIDGZ i_macb1_rx_clk(.PAD(macb1_rx_clk_pad),.C(macb1_rx_clk));
PDIDGZ i_macb2_rx_clk(.PAD(macb2_rx_clk_pad),.C(macb2_rx_clk));
PDIDGZ i_macb3_rx_clk(.PAD(macb3_rx_clk_pad),.C(macb3_rx_clk));

PDIDGZ i_macb0_rx_dv(.PAD(macb0_rx_dv_pad),.C(macb0_rx_dv));
PDIDGZ i_macb1_rx_dv(.PAD(macb1_rx_dv_pad),.C(macb1_rx_dv));
PDIDGZ i_macb2_rx_dv(.PAD(macb2_rx_dv_pad),.C(macb2_rx_dv));
PDIDGZ i_macb3_rx_dv(.PAD(macb3_rx_dv_pad),.C(macb3_rx_dv));

PDIDGZ i_macb_mdio_in(.PAD(macb_mdio_in_pad),.C(macb_mdio_in));

//MACB output pads
PDO04CDG i_macb0_tx_er(.I(macb0_tx_er),.PAD(macb0_tx_er_pad));
PDO04CDG i_macb1_tx_er(.I(macb1_tx_er),.PAD(macb1_tx_er_pad));
PDO04CDG i_macb2_tx_er(.I(macb2_tx_er),.PAD(macb2_tx_er_pad));
PDO04CDG i_macb3_tx_er(.I(macb3_tx_er),.PAD(macb3_tx_er_pad));

generate
for ( i = 0; i <=3 ; i = i+1)
begin : MACB0_TXD
PDO04CDG i_macb0_txd(.I(macb0_txd[i]),.PAD(macb0_txd_pad[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin : MACB1_TXD
PDO04CDG i_macb1_txd(.I(macb1_txd[i]),.PAD(macb1_txd_pad[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin : MACB2_TXD
PDO04CDG i_macb2_txd(.I(macb2_txd[i]),.PAD(macb2_txd_pad[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin : MACB3_TXD
PDO04CDG i_macb3_txd(.I(macb3_txd[i]),.PAD(macb3_txd_pad[i]));
end
endgenerate

PDO04CDG i_macb0_tx_en(.I(macb0_tx_en),.PAD(macb0_tx_en_pad));
PDO04CDG i_macb1_tx_en(.I(macb1_tx_en),.PAD(macb1_tx_en_pad));
PDO04CDG i_macb2_tx_en(.I(macb2_tx_en),.PAD(macb2_tx_en_pad));
PDO04CDG i_macb3_tx_en(.I(macb3_tx_en),.PAD(macb3_tx_en_pad));

PDO04CDG i_macb_mdc(.I(macb_mdc),.PAD(macb_mdc_pad));
PDO04CDG i_macb_mdio_out(.I(macb_mdio_out),.PAD(macb_mdio_out_pad));
PDO04CDG i_macb_mdio_en(.I(macb_mdio_en),.PAD(macb_mdio_en_pad));

PDIDGZ i_ua_NCTS(.PAD(ua_NCTS_pad),.C(ua_ncts));
PDIDGZ i_ua_RXDA(.PAD(ua_RXDA_pad),.C(ua_rxd));
PDIDGZ i_ua_NCTS1(.PAD(ua_NCTS1_pad),.C(ua_ncts1));
PDIDGZ i_ua_RXDA1(.PAD(ua_RXDA1_pad),.C(ua_rxd1));

PDIDGZ i_jtag_NTRST(.PAD(jtag_NTRST_pad),.C(jtag_ntrst));
PDIDGZ i_jtag_TCK(.PAD(jtag_TCK_pad),.C(jtag_tck));
PDIDGZ i_jtag_TMS(.PAD(jtag_TMS_pad),.C(jtag_tms));
PDIDGZ i_jtag_TDI(.PAD(jtag_TDI_pad),.C(jtag_tdi));
PDIDGZ i_shift_en(.PAD(shift_en_pad),.C(shift_en));

PDIDGZ i_spi_N_ss_in(.PAD(spi_N_ss_in_pad),.C(n_ss_in));



PDB04DGZ i_ua_TXDA (.I(ua_txd),  .OEN(scan_mode_pf),.PAD(ua_TXDA_pad),  .C(scan_chain_in_12));
PDB04DGZ i_ua_NRTS (.I(ua_nrts), .OEN(scan_mode_pf),.PAD(ua_NRTS_pad),  .C(scan_chain_in_13));
PDB04DGZ i_ua_TXDA1(.I(ua_txd1), .OEN(scan_mode_pf),.PAD(ua_TXDA_pad1), .C(scan_chain_in_14));
PDB04DGZ i_ua_NRTS1(.I(ua_nrts1),.OEN(scan_mode_pf),.PAD(ua_NRTS_pad1), .C(scan_chain_in_15));



PDISDGZ i_pin_rst(.PAD(pin_reset_pad),.C(pin_reset));
PDIDGZ i_pin_32K(.PAD(pin_32k_pad),.C(pin_32k));
PDIDGZ i_pin_SYSCLK(.PAD(pin_sysclk_pad),.C(pin_sysclk));
PDIDGZ i_pin_12M(.PAD(pin_12M_pad),.C(pin_12M));
PDIDGZ i_pin_MBIST(.PAD(MBIST_en_pad),.C(MBIST_en));

PDO04CDG i_rf_rstn(.I(rf_reset_n),.PAD(rf_resetn_pad));
PDO04CDG i_rf_EN  (.I(rf_en),     .PAD(rf_en_pad));

generate
for ( i = 0; i <=3 ; i = i+1)
begin :rf_SW
PDO04CDG i_rf_SW(.I(rf_sw[i]),.PAD(rf_sw_pad[i]));
end
endgenerate

PDT04DGZ i_jtag_TDO(.I(jtag_tdo),.OEN(jtag_oe),.PAD(jtag_TDO_pad));

generate
for ( i = 1; i <=P_SIZE ; i = i+1)
begin :spi_N
PDT04DGZ i_spi_N_ss_out(.I(n_ss_out[i-1]),.OEN(n_ss_en),.PAD(spi_N_ss_out_pad[i-1]));
end
endgenerate


generate
for ( i = 0; i <=15 ; i = i+1)
begin : SMC_addr
PDO04CDG i_SMC_addr(.I(smc_addr[i]),.PAD(SMC_addr_pad[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin :SMC_n_be
PDO04CDG i_SMC_n_be(.I(smc_n_be[i]),.PAD(SMC_n_be_pad[i]));
end
endgenerate

generate
for ( i = 0; i <=3 ; i = i+1)
begin :SMC_n_we
PDO04CDG i_SMC_n_we(.I(smc_n_we[i]),.PAD(SMC_n_we_pad[i]));
end
endgenerate


PDO04CDG i_SMC_n_CS(.I(smc_n_cs),.PAD(SMC_n_CS_pad));

PDO04CDG i_SMC_n_wr(.I(smc_n_wr),.PAD(SMC_n_wr_pad));
PDO04CDG i_SMC_n_rd(.I(smc_n_rd),.PAD(SMC_n_rd_pad));

generate
for ( i = 0; i <=15 ; i = i+1)
begin : GPIO
assign gpio_pin_out_mux[i]  = scan_mode_pf ? scan_chain_out_[i] : gpio_pin_out[i];
assign n_gpio_pin_oe_mux[i] = scan_mode_pf ?     1'b0     : n_gpio_pin_oe[i];
PDB04SDGZ i_GPIO(.I(gpio_pin_out_mux[i]),.OEN(n_gpio_pin_oe_mux[i]), .PAD(GPIO_pad [i]),.C(gpio_pin_in[i])); 
end
endgenerate


assign n_so_en_mux   = scan_mode_pf ?     1'b1     : n_so_en;
assign n_mo_en_mux   = scan_mode_pf ?     1'b1     : n_mo_en;
assign n_sclk_en_mux = scan_mode_pf ?     1'b1     : n_sclk_en;
PDB04DGZ i_spi_SOMI(.I(so),       .OEN(n_so_en_mux),   .PAD(spi_SOMI_pad), .C(mi));
PDB04DGZ i_spi_SIMO(.I(mo),       .OEN(n_mo_en_mux),   .PAD(spi_SIMO_pad), .C(si));
PDB04DGZ i_spi_CLK (.I(sclk_out), .OEN(n_sclk_en_mux), .PAD(spi_CLK_pad),  .C(sclk_in));

generate
for ( i = 0; i <=31 ; i = i+1)
begin : SMC_data
PRB08DGZ i_SMC_data(.I(smc_data[i]),.OEN(smc_n_ext_oe),.PAD(SMC_data_pad[i]),.C(data_smc[i]));
end
endgenerate

lvds  i_lvds(
.hiss_rxi(hiss_rxi), 
.hiss_rxien(hiss_rxien),
.hissrxip(hissrxip),
.hissrxin(hissrxin),
.hiss_clk(hiss_clk),
.hiss_clken(hiss_clken),
.hissclkp(hissclkp), 
.hiss_rxq(hiss_rxq),
.hiss_rxqen(hiss_rxqen), 
.hissclkn(hissclkn),
.hissrxqp(hissrxqp), 
.hissrxqn(hissrxqn),
.vdd_hiss(vdd_hiss),
.vss_hiss(vss_hiss),
.vsub_hiss(vsub_hiss),
.hiss_biasen(hiss_biasen),
.hiss_replien(hiss_replien),
.hiss_curr(hiss_curr),
.hisstxip(hisstxip), 
.hisstxin(hisstxin), 
.hiss_txi(hiss_txi), 
.hiss_txien(hiss_txien),
.hisstxqp(hisstxqp),
.hisstxqn(hisstxqn), 
.hiss_txqen(hiss_txqen),
.hiss_txq(hiss_txq)
);


dummy_analog_pad i_pad_dp(
	.from_chip(dp),
	.from_ext(dp_pad)
	);
dummy_analog_pad i_pad_dn(
	.from_chip(dn),
	.from_ext(dn_pad)
	);
dummy_analog_pad i_pad_rref(
	.from_chip(rrefext),
	.from_ext(rrefext_pad)
	);

endmodule
