//File name   : socv.v
//Title       : SoC Top level
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

module socv(
             //inputs
              ua_NCTS_pad,
              ua_RXDA_pad,
              ua_NCTS1_pad,
              ua_RXDA1_pad,
	           shift_en_pad,
              jtag_NTRST_pad,
              jtag_TCK_pad,
              jtag_TMS_pad,
              jtag_TDI_pad,
              spi_N_ss_in_pad,
              pin_reset_pad,
	           pin_sysclk_pad,
	           pin_hclk_pad,

      	     scan_mode,       // Remove once the tap is in place 
	           MBIST_en_pad,
             
             //MACB ports
             //inputs
              macb_mdio_in_pad,    
              macb0_col_pad,        
              macb0_crs_pad,       
              macb0_tx_clk_pad,   
              macb0_rxd_pad,     
              macb0_rx_er_pad,  
              macb0_rx_clk_pad,
              macb0_rx_dv_pad,    
              
                                   
              macb1_col_pad,        
              macb1_crs_pad,       
              macb1_tx_clk_pad,   
              macb1_rxd_pad,     
              macb1_rx_er_pad,  
              macb1_rx_clk_pad,
              macb1_rx_dv_pad,    
              
              
              macb2_col_pad,        
              macb2_crs_pad,       
              macb2_tx_clk_pad,   
              macb2_rxd_pad,     
              macb2_rx_er_pad,  
              macb2_rx_clk_pad,
              macb2_rx_dv_pad,    
              
              
              macb3_col_pad,        
              macb3_crs_pad,       
              macb3_tx_clk_pad,   
              macb3_rxd_pad,     
              macb3_rx_er_pad,  
              macb3_rx_clk_pad,
              macb3_rx_dv_pad,    

             //MACB outputs
              macb_mdc_pad,            
              macb_mdio_out_pad,       
              macb_mdio_en_pad,        

              macb0_tx_er_pad,       
              macb0_txd_pad,        
              macb0_tx_en_pad,     

              macb1_tx_er_pad,       
              macb1_txd_pad,        
              macb1_tx_en_pad,     

              macb2_tx_er_pad,       
              macb2_txd_pad,        
              macb2_tx_en_pad,     

              macb3_tx_er_pad,       
              macb3_txd_pad,        
              macb3_tx_en_pad,     


             //outputs
	           ua_NRTS_pad,
	           ua_TXDA_pad,
	           ua_NRTS1_pad,
	           ua_TXDA1_pad,
              jtag_TDO_pad,
              spi_N_ss_out_pad,
              SMC_n_be_pad,
	           SMC_n_CS_pad,
	           SMC_n_we_pad,
	           SMC_n_wr_pad,
	           SMC_n_rd_pad,
	           SMC_addr_pad,

             //inout
    	        GPIO_pad,
    	        spi_SIMO_pad,
	           spi_SOMI_pad,
	           spi_CLK_pad,
    	        SMC_data_pad,
	           dp_pad,
	           dn_pad,
	           rrefext_pad,
                   core06v,
                   core08v,
                   core10v,
                   core12v
             );


//---------------------------------------------------------------------------//
parameter P_SIZE        = 8;       // number of peripheral select lines
//---------------------------------------------------------------------------//


input 	     ua_NCTS_pad,ua_RXDA_pad;
input 	     ua_NCTS1_pad,ua_RXDA1_pad;
input 	     jtag_NTRST_pad,jtag_TCK_pad,jtag_TMS_pad,jtag_TDI_pad;
input 	     shift_en_pad;
input 	     spi_N_ss_in_pad;
input 	     pin_reset_pad;
input 	     pin_sysclk_pad;
input 	     pin_hclk_pad;
input 	     MBIST_en_pad;
inout 	     ua_NRTS_pad,ua_TXDA_pad;
inout 	     ua_NRTS1_pad,ua_TXDA1_pad;
output 	     jtag_TDO_pad;
output [P_SIZE-1:0] spi_N_ss_out_pad;
output [3:0] SMC_n_be_pad,SMC_n_we_pad;
output 	     SMC_n_wr_pad,SMC_n_rd_pad;
output  SMC_n_CS_pad;
output [15:0]SMC_addr_pad;


// Temporary scan_mode port
input	     scan_mode;

//MACB ports
input         macb0_col_pad;            // collision detect signal from the PHY
input         macb0_crs_pad;            // carrier sense signal from the PHY
input         macb0_tx_clk_pad;         // transmit clock from the PHY
input   [3:0] macb0_rxd_pad;            // receive data from the PHY
input         macb0_rx_er_pad;          // receive error signal from the PHY
input         macb0_rx_clk_pad;         // receive clock from the PHY
input         macb0_rx_dv_pad;          // receive data valid signal from the PHY
input         macb_mdio_in_pad;        // management data input 

output        macb0_tx_er_pad;         
output [3:0]  macb0_txd_pad;           
output        macb0_tx_en_pad;         
output        macb_mdc_pad;            
output        macb_mdio_out_pad;       
output        macb_mdio_en_pad;        


input         macb1_col_pad;      
input         macb1_crs_pad;     
input         macb1_tx_clk_pad; 
input   [3:0] macb1_rxd_pad;   
input         macb1_rx_er_pad;
input         macb1_rx_clk_pad;    
input         macb1_rx_dv_pad;  

output        macb1_tx_er_pad;         
output [3:0]  macb1_txd_pad;           
output        macb1_tx_en_pad;         

input         macb2_col_pad;   
input         macb2_crs_pad;  
input         macb2_tx_clk_pad;    
input   [3:0] macb2_rxd_pad; 
input         macb2_rx_er_pad;   
input         macb2_rx_clk_pad; 
input         macb2_rx_dv_pad; 

output        macb2_tx_er_pad;         
output [3:0]  macb2_txd_pad;           
output        macb2_tx_en_pad;         

input         macb3_col_pad;  
input         macb3_crs_pad; 
input         macb3_tx_clk_pad;    
input   [3:0] macb3_rxd_pad;       
input         macb3_rx_er_pad;  
input         macb3_rx_clk_pad;    
input         macb3_rx_dv_pad; 

output        macb3_tx_er_pad;         
output [3:0]  macb3_txd_pad;           
output        macb3_tx_en_pad;  

inout [15:0] GPIO_pad;
inout         spi_SIMO_pad,spi_SOMI_pad,spi_CLK_pad;
inout [31:0]  SMC_data_pad;
inout 	     dp_pad;
inout 	     dn_pad;
inout         rrefext_pad;

output core06v;
output core08v;
output core10v;
output core12v;
//---------------------------------------------------------------------------//
wire        hclk;      // AHB Clock - 240M
wire        n_hreset;  // AHB reset in 240MHz domain - Active low
wire        pclk;     // APB Clock - 240M
wire        n_preset;  // APB reset - Active low

wire		pin_reset_i;
wire		pin_hclk_i;

// AHB interface
//AHB S0
wire   	   cpu_tcm_hsel;
wire [31:0] cpu_tcm_haddr;
wire [1:0]  cpu_tcm_htrans;
wire        cpu_tcm_hwrite;
wire        cpu_tcm_hready_in;
wire [2:0]  cpu_tcm_hsize;
wire [2:0]  cpu_tcm_hburst;
wire [3:0]  cpu_tcm_hprot;
wire [3:0]  cpu_tcm_hmaster;	
wire [31:0] cpu_tcm_hwdata;
wire        cpu_tcm_hmastlock;
	
wire [31:0] cpu_tcm_hrdata;
wire        cpu_tcm_hready;
wire  [1:0] cpu_tcm_hresp;

//AHB S1
wire        sram_subsystem_hsel;
wire [31:0] sram_subsystem_haddr;
wire [1:0]  sram_subsystem_htrans;
wire [2:0]  sram_subsystem_hsize;
wire        sram_subsystem_hwrite;
wire        sram_subsystem_hready_in;
wire [31:0] sram_subsystem_hwdata;
wire [2:0]  sram_subsystem_hburst;
wire [3:0]  sram_subsystem_hprot;
wire [3:0]  sram_subsystem_hmaster;
wire        sram_subsystem_hmastlock;

wire [31:0] sram_subsystem_hrdata;
wire        sram_subsystem_hready;
wire [1:0]  sram_subsystem_hresp;

//AHB S2
wire        rom_subsystem_hsel;
wire [31:0] rom_subsystem_haddr;
wire [1:0]  rom_subsystem_htrans;
wire [2:0]  rom_subsystem_hsize;
wire        rom_subsystem_hwrite;
wire        rom_subsystem_hready_in;
wire [2:0]  rom_subsystem_hburst;     // Burst type
wire [3:0]  rom_subsystem_hprot;      // Protection control
wire [3:0]  rom_subsystem_hmaster;    // Master select
wire [31:0] rom_subsystem_hwdata;    // Write Data
wire        rom_subsystem_hmastlock;  // Locked transfer
  
wire [31:0] rom_subsystem_hrdata;
wire        rom_subsystem_hready;
wire [1:0]  rom_subsystem_hresp;

//AHB S3
wire        ahb2apb0_hsel;     // AHB2APB select
wire [31:0] ahb2apb0_haddr;    // Address bus
wire [1:0]  ahb2apb0_htrans;   // Transfer type
wire [2:0]  ahb2apb0_hsize;    // AHB Access type - byte, half-word, word
wire [31:0] ahb2apb0_hwdata;   // Write data
wire        ahb2apb0_hwrite;   // Write signal/
wire        ahb2apb0_hready_in;// Indicates that last master has finished bus access
wire [2:0]  ahb2apb0_hburst;     // Burst type
wire [3:0]  ahb2apb0_hprot;      // Protection control
wire [3:0]  ahb2apb0_hmaster;    // Master select
wire        ahb2apb0_hmastlock;  // Locked transfer

wire [31:0] ahb2apb0_hrdata; 
wire        ahb2apb0_hready;
wire [1:0]  ahb2apb0_hresp; 
	
// SMC AHB interface
//AHB S4
wire        smc_hclk;
wire        smc_n_hclk;
wire        smc_hsel;
wire [31:0] smc_haddr;
wire [1:0]  smc_htrans;
wire        smc_hwrite;
wire [2:0]  smc_hsize;
wire [31:0] smc_hwdata;
wire        smc_hready_in;
wire [2:0]  smc_hburst;     // Burst type
wire [3:0]  smc_hprot;      // Protection control
wire [3:0]  smc_hmaster;    // Master select
wire        smc_hmastlock;  // Locked transfer

wire [31:0] smc_hrdata; 
wire        smc_hready;
wire [1:0]  smc_hresp;


//AHB S5
wire            dma_s_hsel;
wire [31:0]     dma_s_haddr;
wire [1:0]      dma_s_htrans;
wire            dma_s_hwrite;
wire [2:0]      dma_s_hsize;
wire            dma_s_hready_in; 		// Transfer done
wire [2:0]      dma_s_hburst;    // Burst type
wire [3:0]      dma_s_hprot;     // Protection control
wire [3:0]      dma_s_hmaster;   // Master select
wire            dma_s_hmastlock; // Locked transfer
wire [31:0]     dma_s_hwdata;

wire [31:0]     dma_s_hrdata;
wire            dma_s_hready;
wire [1:0]      dma_s_hresp;

//AHB S6
wire        ahb2apb1_hsel;     // AHB2APB select
wire [31:0] ahb2apb1_haddr;    // Address bus
wire [1:0]  ahb2apb1_htrans;   // Transfer type
wire [2:0]  ahb2apb1_hsize;    // AHB Access type - byte, half-word, word
wire [31:0] ahb2apb1_hwdata;   // Write data
wire        ahb2apb1_hwrite;   // Write signal/
wire        ahb2apb1_hready_in;// Indicates that last master has finished bus access
wire [2:0]  ahb2apb1_hburst;     // Burst type
wire [3:0]  ahb2apb1_hprot;      // Protection control
wire [3:0]  ahb2apb1_hmaster;    // Master select
wire        ahb2apb1_hmastlock;  // Locked transfer

wire [31:0] ahb2apb1_hrdata; 
wire        ahb2apb1_hready;
wire [1:0]  ahb2apb1_hresp; 

//AHB S8
wire   	    ahb2ocp_hsel;
wire [31:0] ahb2ocp_haddr;
wire [1:0]  ahb2ocp_htrans;
wire        ahb2ocp_hwrite;
wire        ahb2ocp_hready_in;
wire [2:0]  ahb2ocp_hsize;
wire [2:0]  ahb2ocp_hburst;
wire [3:0]  ahb2ocp_hprot;
wire [3:0]  ahb2ocp_hmaster;	
wire [31:0] ahb2ocp_hwdata;
wire        ahb2ocp_hmastlock;

wire [31:0] ahb2ocp_hrdata;
wire        ahb2ocp_hready;
wire  [1:0] ahb2ocp_hresp;

wire [1:0] ao_sresp_i;
wire       ao_sresplast_i;
wire [2:0] ao_mcmd_o;
wire [27:0] ao_maddr_o;
wire [4:0] ao_matomic_length_o;
wire [4:0] ao_mburstlength_o;
wire [2:0]  ao_mburst_seq_o;
wire [2:0]  ao_mtag_id_o;
wire [2:0]  ao_mdata_tag_id_o;
wire [127:0]  ao_mdata_o;
wire [127:0]  ao_sdata_i;
wire          ao_sdataaccept_i;
wire          ao_scmdaccept_i;


//DMA master signals
//AHB M0
wire [31:0]     dma_m_haddr;
wire [1:0]      dma_m_htrans;
wire            dma_m_hwrite;
wire [2:0]      dma_m_hsize;
wire [2:0]      dma_m_hburst;
wire [3:0]      dma_m_hprot;
wire [31:0]     dma_m_hwdata;
wire            dma_m_hlock;
wire [31:0]     dma_m_hrdata;
wire            dma_m_hready;
wire [1:0]      dma_m_hresp;
wire            dma_irq;

//AHB M1
wire [31:0] cpu_biu_haddr;
wire [1:0]  cpu_biu_htrans;
wire        cpu_biu_hwrite;
wire [2:0]  cpu_biu_hsize;
wire [2:0]  cpu_biu_hburst;
wire [3:0]  cpu_biu_hprot;
wire [31:0] cpu_biu_hwdata;
wire        cpu_biu_hlock;
wire [31:0] cpu_biu_hrdata;
wire        cpu_biu_hready;
wire  [1:0] cpu_biu_hresp;

//AHB M2
wire [31:0] macb0_haddr;
wire [1:0]  macb0_htrans;
wire        macb0_hwrite;
wire [2:0]  macb0_hsize;
wire [2:0]  macb0_hburst;
wire [3:0]  macb0_hprot;
wire [31:0] macb0_hwdata;
wire        macb0_hlock;
wire [31:0] macb0_hrdata;
wire        macb0_hready;
wire  [1:0] macb0_hresp;

//AHB M3
wire   	   macb1_hsel;
wire [31:0] macb1_haddr;
wire [1:0]  macb1_htrans;
wire        macb1_hwrite;
wire [2:0]  macb1_hsize;
wire [2:0]  macb1_hburst;
wire [3:0]  macb1_hprot;
wire [31:0] macb1_hwdata;
wire        macb1_hlock;
wire [31:0] macb1_hrdata;
wire        macb1_hready;
wire  [1:0] macb1_hresp;

//AHB M4
wire   	   macb2_hsel;
wire [31:0] macb2_haddr;
wire [1:0]  macb2_htrans;
wire        macb2_hwrite;
wire [2:0]  macb2_hsize;
wire [2:0]  macb2_hburst;
wire [3:0]  macb2_hprot;
wire [31:0] macb2_hwdata;
wire        macb2_hlock;
wire [31:0] macb2_hrdata;
wire        macb2_hready;
wire  [1:0] macb2_hresp;

//AHB M5
wire   	   macb3_hsel;
wire [31:0] macb3_haddr;
wire [1:0]  macb3_htrans;
wire [2:0]  macb3_hsize;
wire [2:0]  macb3_hburst;
wire [3:0]  macb3_hprot;
wire [31:0] macb3_hwdata;
wire        macb3_hlock;
wire [31:0] macb3_hrdata;
wire        macb3_hready;
wire  [1:0] macb3_hresp;

wire        dma_m_hready_out;
wire        cpu_biu_hready_out;
wire        macb0_hready_out;
wire        macb1_hready_out;
wire        macb2_hready_out;
wire        macb3_hready_out;

//APB1 wires
wire		   apb1_pwrite;
wire		   apb1_penable;
wire [31:0]	apb1_pwdata;
wire [31:0]	apb1_paddr;
wire        psel_mac0;
wire        psel_mac1;
wire        psel_mac2;
wire        psel_mac3;
wire [31:0]	prdata_mac0;
wire [31:0]	prdata_mac1;
wire [31:0]	prdata_mac2;
wire [31:0]	prdata_mac3;


wire         macb0_col, macb1_col, macb2_col, macb3_col; 
wire         macb0_crs,macb1_crs, macb2_crs, macb3_crs;  
wire         macb0_tx_clk, macb1_tx_clk, macb2_tx_clk, macb3_tx_clk; 
wire   [3:0] macb0_rxd, macb1_rxd, macb2_rxd, macb3_rxd;   
wire         macb0_rx_er, macb1_rx_er, macb2_rx_er, macb3_rx_er;
wire         macb0_rx_clk, macb1_rx_clk, macb2_rx_clk, macb3_rx_clk; 
wire         macb0_rx_dv, macb1_rx_dv, macb2_rx_dv, macb3_rx_dv; 
wire         macb_mdio_in; 

wire        macb0_tx_er, macb1_tx_er, macb2_tx_er, macb3_tx_er;         
wire [3:0]  macb0_txd, macb1_txd, macb2_txd, macb3_txd;           
wire        macb0_tx_en, macb1_tx_en, macb2_tx_en, macb3_tx_en;         
wire        macb_mdc;            
wire        macb_mdio_out;       
wire        macb_mdio_en;        

wire        macb0_int, macb1_int, macb2_int, macb3_int;
wire        macb0_wakeup, macb1_wakeup, macb2_wakeup, macb3_wakeup;

wire        macb0_lp_local, macb0_lclk;
wire        macb1_lp_local, macb1_lclk;
wire        macb2_lp_local, macb2_lclk;
wire        macb3_lp_local, macb3_lclk;

wire [31:0] data_smc;     // EMI(External memory) read data
wire [15:0] smc_addr;      // External Memory (EMI) address
wire [3:0]  smc_n_be;      // EMI byte enables (Active LOW)
wire        smc_n_cs;      // EMI Chip Selects (Active LOW)
wire [3:0]  smc_n_we;      // EMI write strobes (Active LOW)
wire        smc_n_wr;      // EMI write enable (Active LOW)
wire        smc_n_rd;      // EMI read stobe (Active LOW)
wire        smc_n_ext_oe;  // EMI write data output enable
wire [31:0] smc_data;      // EMI write data

wire        ua_rxd;       // UART receiver serial input pin
wire        ua_rxd1;       // UART receiver serial input pin
wire        ua_ncts;      // Clear-To-Send flow control
wire        ua_ncts1;      // Clear-To-Send flow control
wire        n_ss_in;      // select input to slave(spi)
wire        mi;           // data input to master(spi)
wire        si;           // data input to slave(spi)
wire        sclk_in;      // clock input to slave(spi)
wire        arm_nfiq;     // Fiq interrupt output 
wire        arm_nirq;     // Irq interrupt output 
wire        ua_txd;       // UART transmitter serial output
wire        ua_txd1;       // UART transmitter serial output
wire        ua_nrts;      // Request-To-Send flow control
wire        ua_nrts1;      // Request-To-Send flow control
wire        so;                    // data output from slave
wire        mo;                    // data output from master
wire        sclk_out;              // clock output from master
wire [P_SIZE-1:0] n_ss_out;    // peripheral select lines from master
wire        n_so_en;               // out enable for slave data
wire        n_mo_en;               // out enable for master data
wire        n_sclk_en;             // out enable for master clock
wire        n_ss_en;               // out enable for master peripheral lines
wire [15:0] n_gpio_pin_oe;    // output enable signal to pin
wire [15:0] gpio_pin_out;     // output signal to pin
wire [15:0]  gpio_pin_in;             // input data from pin

wire        jtag_tdo;
wire        jtag_oe;
wire        jtag_tck;
wire        jtag_tms;
wire        jtag_tdi;
wire        jtag_ntrst;
wire        scan_mode;

//    USB Connections 
wire		       dp;
wire		       dn;
wire		       rrefext;
wire		       pin_sysclk_i;

wire [21:2]	    cpu_itcm_addr;
wire [31:0]	    cpu_itcm_rdata;
wire [31:0]	    cpu_itcm_wdata;
wire          	 cpu_itcm_cs;
wire  [3:0]     cpu_itcm_we;
wire  [4:0]     cpu_itcm_size;
wire  [4:0]     cpu_dtcm_size;
wire [21:3]	    cpu_d0tcm_addr;
wire [31:0]	    cpu_d0tcm_rdata;
wire [31:0]	    cpu_d0tcm_wdata;
wire          	 cpu_d0tcm_cs;
wire  [3:0]     cpu_d0tcm_we;
wire [21:3]	    cpu_d1tcm_addr;
wire [31:0]	    cpu_d1tcm_rdata;
wire [31:0]	    cpu_d1tcm_wdata;
wire          	 cpu_d1tcm_cs;
wire  [3:0]     cpu_d1tcm_we;

// Local wire decalarion
wire [31:0]	hrdata_apb0 ;
wire    	hready_apb0 ;
wire [ 1:0]   	hresp_apb0  ; 
wire [31:0]	hrdata_apb1 ;
wire    	hready_apb1 ;
wire [ 1:0]   	hresp_apb1  ; 

wire  [2:0] tie_lo_bus3;       // to tie EMA of SRAM
wire        tie_lo_1bit;
wire [1:0]  tie_lo_2bit;
wire [3:0]  tie_lo_4bit;
wire [31:0] tie_lo_32bit;
wire [15:0] tie_lo_16bit;
wire 	    tie_hi_1bit;

// the following signals are to zeroise htrans from bus matrix if hsel is zero
wire [1:0] cpu_tcm_htrans_raw;
wire [1:0] sram_subsystem_htrans_raw;
wire [1:0] rom_subsystem_htrans_raw;
wire [1:0] ahb2apb0_htrans_raw;
wire [1:0] smc_htrans_raw;
wire [1:0] dma_s_htrans_raw;
wire [1:0] ahb2apb1_htrans_raw;
wire [1:0] ahb2ocp_htrans_raw;
//---------------------------------------------------------------------------//
assign tie_lo_bus3 = 3'b000;
assign tie_lo_1bit =1'b0;
assign tie_lo_2bit =2'b0;
assign tie_lo_4bit =4'b0;
assign tie_lo_32bit=32'b0;
assign tie_hi_1bit =1'b1;
assign tie_lo_16bit= 16'b0;

assign n_preset = n_hreset;  // hreset and preset and the same

assign cpu_itcm_size = 5'b00101;  // NEW 4K  words -> 16KBytes
assign cpu_dtcm_size = 5'b00111;  // NEW  and 16K words -> 64KBytes

assign jtag_tdo = 1'b0;
assign jtag_oe  = 1'b1;

assign smc_hclk   = hclk;
assign smc_n_hclk = ~hclk;
assign pclk = hclk;
assign hclk =  pin_hclk_i;

assign n_hreset  = pin_reset_i;

//---------------------------------------------------------------------------//

padframe i_pad_frame(
              //inputs
              .ua_NCTS_pad(ua_NCTS_pad),
              .ua_RXDA_pad(ua_RXDA_pad),
              .ua_NCTS1_pad(ua_NCTS1_pad),
              .ua_RXDA1_pad(ua_RXDA1_pad),
              .ua_txd(ua_txd),
              .ua_txd1(ua_txd1),
              .ua_nrts(ua_nrts),
              .ua_nrts1(ua_nrts1), 
	      .shift_en_pad(shift_en_pad),
	      .shift_en(),
	      .MBIST_en_pad(MBIST_en_pad),
	      .MBIST_en(),
	      .scan_mode_pf(scan_mode),  // scan mode input for padframe. 
	      .scan_chain_in_(),		// Pins that feed the 16 Scan chains
	      .scan_chain_out_(),		// Pins that are fed by the 16 scan chains
              .jtag_NTRST_pad(jtag_NTRST_pad),
              .jtag_TCK_pad(jtag_TCK_pad),
              .jtag_TMS_pad(jtag_TMS_pad),
              .jtag_TDI_pad(jtag_TDI_pad),
              .jtag_tdo(jtag_tdo),
              .jtag_oe(jtag_oe),
    	      .gpio_pin_out(gpio_pin_out),
              .n_gpio_pin_oe(n_gpio_pin_oe),
              .spi_N_ss_in_pad(spi_N_ss_in_pad),
              .so(so),
              .mo(mo),
              .sclk_out(sclk_out),
              .n_sclk_en(n_sclk_en),
	      .n_so_en(n_so_en),
	      .n_mo_en(n_mo_en),
              .n_ss_en(n_ss_en),
              .n_ss_out(n_ss_out),
              .smc_n_be(smc_n_be),
              .smc_addr(smc_addr), 
              .smc_n_cs(smc_n_cs),
              .smc_n_we(smc_n_we),
              .smc_n_wr(smc_n_wr),
              .smc_n_rd(smc_n_rd),
              .smc_data(smc_data),
              .smc_n_ext_oe(smc_n_ext_oe),
	           .rf_reset_n(),
              .rf_resetn_pad(),
	           .rf_en(),
	           .rf_en_pad(),
	           .rf_sw(),
	           .rf_sw_pad(),
	           .hiss_rxien(), 
              .hiss_rxqen(), 
              .hiss_clken(), 
              .hissrxip(), 
              .hissrxin(), 
              .hissclkp(), 
              .hissclkn(), 
              .hissrxqp(), 
              .hissrxqn(),
              .vdd_hiss(tie_hi_1bit), 
              .vss_hiss(tie_lo_1bit), 
              .vsub_hiss(tie_lo_1bit), 
              .hiss_biasen(), 
              .hiss_replien(), 
              .hiss_curr(),
              .hiss_txi(), 
              .hiss_txq(), 
              .hiss_txien(), 
              .hiss_txqen(),

              .macb0_col_pad(macb0_col_pad),        
              .macb0_crs_pad(macb0_crs_pad),       
              .macb0_tx_clk_pad(macb0_tx_clk_pad),   
              .macb0_rxd_pad(macb0_rxd_pad),     
              .macb0_rx_er_pad(macb0_rx_er_pad),  
              .macb0_rx_clk_pad(macb0_rx_clk_pad),
              .macb0_rx_dv_pad(macb0_rx_dv_pad),    
              .macb_mdio_in_pad(macb_mdio_in_pad),    
              
              .macb0_tx_er(macb0_tx_er),       
              .macb0_txd(macb0_txd),        
              .macb0_tx_en(macb0_tx_en),     
              .macb_mdc(macb_mdc),            
              .macb_mdio_out(macb_mdio_out),       
              .macb_mdio_en(macb_mdio_en),        
                                   
              .macb1_col_pad(macb1_col_pad),        
              .macb1_crs_pad(macb1_crs_pad),       
              .macb1_tx_clk_pad(macb1_tx_clk_pad),   
              .macb1_rxd_pad(macb1_rxd_pad),     
              .macb1_rx_er_pad(macb1_rx_er_pad),  
              .macb1_rx_clk_pad(macb1_rx_clk_pad),
              .macb1_rx_dv_pad(macb1_rx_dv_pad),    
              
              .macb1_tx_er(macb1_tx_er),       
              .macb1_txd(macb1_txd),        
              .macb1_tx_en(macb1_tx_en),     
              
              .macb2_col_pad(macb2_col_pad),        
              .macb2_crs_pad(macb2_crs_pad),       
              .macb2_tx_clk_pad(macb2_tx_clk_pad),   
              .macb2_rxd_pad(macb2_rxd_pad),     
              .macb2_rx_er_pad(macb2_rx_er_pad),  
              .macb2_rx_clk_pad(macb2_rx_clk_pad),
              .macb2_rx_dv_pad(macb2_rx_dv_pad),    
              
              .macb2_tx_er(macb2_tx_er),       
              .macb2_txd(macb2_txd),        
              .macb2_tx_en(macb2_tx_en),     

              .macb3_col_pad(macb3_col_pad),        
              .macb3_crs_pad(macb3_crs_pad),       
              .macb3_tx_clk_pad(macb3_tx_clk_pad),   
              .macb3_rxd_pad(macb3_rxd_pad),     
              .macb3_rx_er_pad(macb3_rx_er_pad),  
              .macb3_rx_clk_pad(macb3_rx_clk_pad),
              .macb3_rx_dv_pad(macb3_rx_dv_pad),    

              .macb3_tx_er(macb3_tx_er),       
              .macb3_txd(macb3_txd),        
              .macb3_tx_en(macb3_tx_en),    

              //outputs
    	        .ua_ncts(ua_ncts),
    	        .ua_ncts1(ua_ncts1),
	           .ua_rxd(ua_rxd),
	           .ua_rxd1(ua_rxd1),
	           .ua_NRTS_pad(ua_NRTS_pad),
	           .ua_TXDA_pad(ua_TXDA_pad),
	           .ua_NRTS_pad1(ua_NRTS1_pad),
	           .ua_TXDA_pad1(ua_TXDA1_pad),
	           .pin_reset(pin_reset_i),
              .pin_reset_pad(pin_reset_pad),
	           .pin_32k(),
 	           .pin_32k_pad(),
	           .pin_sysclk(pin_sysclk_i),
 	           .pin_sysclk_pad(pin_sysclk_pad),
	           .pin_12M(pin_hclk_i),
 	           .pin_12M_pad(pin_hclk_pad),
              .jtag_TDO_pad(jtag_TDO_pad),
	           .jtag_tck(jtag_tck),
              .jtag_tms(jtag_tms),
              .jtag_tdi(jtag_tdi),
              .jtag_ntrst(jtag_ntrst),
              .gpio_pin_in(gpio_pin_in),
              .n_ss_in(n_ss_in),
              .mi(mi),
              .si(si),
              .sclk_in(sclk_in),
              .spi_N_ss_out_pad(spi_N_ss_out_pad),
              .SMC_n_be_pad(SMC_n_be_pad),
      	     .SMC_n_CS_pad(SMC_n_CS_pad),
	           .SMC_n_we_pad(SMC_n_we_pad),
	           .SMC_n_wr_pad(SMC_n_wr_pad),
	           .SMC_n_rd_pad(SMC_n_rd_pad),
	           .SMC_addr_pad(SMC_addr_pad),
	           .data_smc(data_smc),
	           .hisstxip(), 
	           .hisstxin(), 
	           .hisstxqp(), 
	           .hisstxqn(),
	           .hiss_rxi(), 
	           .hiss_rxq(), 
	           .hiss_clk(),

              .macb0_col(macb0_col),        
              .macb0_crs(macb0_crs),       
              .macb0_tx_clk(macb0_tx_clk),   
              .macb0_rxd(macb0_rxd),     
              .macb0_rx_er(macb0_rx_er),  
              .macb0_rx_clk(macb0_rx_clk),
              .macb0_rx_dv(macb0_rx_dv),    
              .macb_mdio_in(macb_mdio_in),    
              
              .macb0_tx_er_pad(macb0_tx_er_pad),       
              .macb0_txd_pad(macb0_txd_pad),        
              .macb0_tx_en_pad(macb0_tx_en_pad),     
              .macb_mdc_pad(macb_mdc_pad),            
              .macb_mdio_out_pad(macb_mdio_out_pad),       
              .macb_mdio_en_pad(macb_mdio_en_pad),        
                                   
              .macb1_col(macb1_col),        
              .macb1_crs(macb1_crs),       
              .macb1_tx_clk(macb1_tx_clk),   
              .macb1_rxd(macb1_rxd),     
              .macb1_rx_er(macb1_rx_er),  
              .macb1_rx_clk(macb1_rx_clk),
              .macb1_rx_dv(macb1_rx_dv),    
              
              .macb1_tx_er_pad(macb1_tx_er_pad),       
              .macb1_txd_pad(macb1_txd_pad),        
              .macb1_tx_en_pad(macb1_tx_en_pad),    
              
              .macb2_col(macb2_col),        
              .macb2_crs(macb2_crs),       
              .macb2_tx_clk(macb2_tx_clk),   
              .macb2_rxd(macb2_rxd),     
              .macb2_rx_er(macb2_rx_er),  
              .macb2_rx_clk(macb2_rx_clk),
              .macb2_rx_dv(macb2_rx_dv),    
              
              .macb2_tx_er_pad(macb2_tx_er_pad),       
              .macb2_txd_pad(macb2_txd_pad),        
              .macb2_tx_en_pad(macb2_tx_en_pad),    

              .macb3_col(macb3_col),        
              .macb3_crs(macb3_crs),       
              .macb3_tx_clk(macb3_tx_clk),   
              .macb3_rxd(macb3_rxd),     
              .macb3_rx_er(macb3_rx_er),  
              .macb3_rx_clk(macb3_rx_clk),
              .macb3_rx_dv(macb3_rx_dv),    

              .macb3_tx_er_pad(macb3_tx_er_pad),       
              .macb3_txd_pad(macb3_txd_pad),        
              .macb3_tx_en_pad(macb3_tx_en_pad),    


              //inout
    	        .GPIO_pad(GPIO_pad),
    	        .spi_SIMO_pad(spi_SIMO_pad),
	           .spi_SOMI_pad(spi_SOMI_pad),
	           .spi_CLK_pad(spi_CLK_pad),
    	        .SMC_data_pad(SMC_data_pad),
	           // USB Pins
	           .dp(dp),
	           .dp_pad(dp_pad),
	           .dn(dn),
	           .dn_pad(dn_pad),
	           .rrefext(rrefext),
	           .rrefext_pad(rrefext_pad)
     );



//-----------AHB Busmatrix related signals----------------------------
assign dma_s_htrans = dma_s_hsel ? dma_s_htrans_raw : 2'b0;
assign smc_htrans = smc_hsel ? smc_htrans_raw : 2'b0;
assign ahb2apb0_htrans = ahb2apb0_hsel ? ahb2apb0_htrans_raw : 2'b0;
assign rom_subsystem_htrans = rom_subsystem_hsel ? rom_subsystem_htrans_raw : 2'b0;
assign sram_subsystem_htrans = sram_subsystem_hsel ? sram_subsystem_htrans_raw : 2'b0;
assign cpu_tcm_htrans = cpu_tcm_hsel ? cpu_tcm_htrans_raw : 2'b0;
assign ahb2apb1_htrans = ahb2apb1_hsel ? ahb2apb1_htrans_raw : 2'b0;
assign ahb2ocp_htrans = ahb2ocp_hsel ? ahb2ocp_htrans_raw : 2'b0;
    
BusMatrix i_BusMatrix(
    .HCLK(hclk),                // AHB System Clock
    .HRESETn(n_hreset),         // AHB System Reset

    // System Address Remap control
    .REMAP(tie_lo_1bit),        // System REMAP signal

    // DMA master signals to busmatrix
    .HSELS0(tie_hi_1bit),      		// Slave Select
    .HADDRS0(dma_m_haddr),     		// Address bus
    .HTRANSS0(dma_m_htrans),    	// Transfer type 
    .HWRITES0(dma_m_hwrite),    	// Transfer direction
    .HSIZES0(dma_m_hsize),     		// Transfer size
    .HBURSTS0(dma_m_hburst),    	// Burst type
    .HPROTS0(dma_m_hprot),     		// Protection control
    .HMASTERS0(tie_lo_4bit),   		// Master select
    .HWDATAS0(dma_m_hwdata),    	// Write data
    .HMASTLOCKS0(dma_m_hlock), 		// Locked transfer
    .HREADYS0(dma_m_hready),  	// Transfer done

    // CPU master signals to busmatrix
    .HSELS1(tie_hi_1bit),       	// Slave Select
    .HADDRS1(cpu_biu_haddr),      	// Address bus
    .HTRANSS1(cpu_biu_htrans),     	// Transfer type 
    .HWRITES1(cpu_biu_hwrite),     	// Transfer direction
    .HSIZES1(cpu_biu_hsize),      	// Transfer size
    .HBURSTS1(cpu_biu_hburst),     	// Burst type
    .HPROTS1(cpu_biu_hprot),      	// Protection control
    .HMASTERS1(tie_lo_4bit),    	// Master select
    .HWDATAS1(cpu_biu_hwdata),     	// Write data
    .HMASTLOCKS1(cpu_biu_hlock),  	// Locked transfer
    .HREADYS1(cpu_biu_hready),     	// Transfer done

    // MACB0 master signals to busmatrix
    .HSELS2(tie_hi_1bit),      		// Slave Select
    .HADDRS2(macb0_haddr),     		// Address bus
    .HTRANSS2(macb0_htrans),    	// Transfer type 
    .HWRITES2(macb0_hwrite),    	// Transfer direction
    .HSIZES2(macb0_hsize),     		// Transfer size
    .HBURSTS2(macb0_hburst),    	// Burst type
    .HPROTS2(macb0_hprot),     		// Protection control
    .HMASTERS2(tie_lo_4bit),   		// Master select
    .HWDATAS2(macb0_hwdata),    	// Write data
    .HMASTLOCKS2(macb0_hlock), 		// Locked transfer
    .HREADYS2(macb0_hready),  	// Transfer done

    // MACB1 master signals to busmatrix
    .HSELS3(tie_hi_1bit),      		// Slave Select
    .HADDRS3(macb1_haddr),     		// Address bus
    .HTRANSS3(macb1_htrans),    	// Transfer type 
    .HWRITES3(macb1_hwrite),    	// Transfer direction
    .HSIZES3(macb1_hsize),     		// Transfer size
    .HBURSTS3(macb1_hburst),    	// Burst type
    .HPROTS3(macb1_hprot),     		// Protection control
    .HMASTERS3(tie_lo_4bit),   		// Master select
    .HWDATAS3(macb1_hwdata),    	// Write data
    .HMASTLOCKS3(macb1_hlock), 		// Locked transfer
    .HREADYS3(macb1_hready),  	// Transfer done

    // MACB2 master signals to busmatrix
    .HSELS4(tie_hi_1bit),      		// Slave Select
    .HADDRS4(macb2_haddr),     		// Address bus
    .HTRANSS4(macb2_htrans),    	// Transfer type 
    .HWRITES4(macb2_hwrite),    	// Transfer direction
    .HSIZES4(macb2_hsize),     		// Transfer size
    .HBURSTS4(macb2_hburst),    	// Burst type
    .HPROTS4(macb2_hprot),     		// Protection control
    .HMASTERS4(tie_lo_4bit),   		// Master select
    .HWDATAS4(macb2_hwdata),    	// Write data
    .HMASTLOCKS4(macb2_hlock), 		// Locked transfer
    .HREADYS4(macb2_hready),  	// Transfer done

    // MACB3 master signals to busmatrix
    .HSELS5(tie_hi_1bit),      		// Slave Select
    .HADDRS5(macb3_haddr),     		// Address bus
    .HTRANSS5(macb3_htrans),    	// Transfer type 
    .HWRITES5(macb3_hwrite),    	// Transfer direction
    .HSIZES5(macb3_hsize),     		// Transfer size
    .HBURSTS5(macb3_hburst),    	// Burst type
    .HPROTS5(macb3_hprot),     		// Protection control
    .HMASTERS5(tie_lo_4bit),   		// Master select
    .HWDATAS5(macb3_hwdata),    	// Write data
    .HMASTLOCKS5(macb3_hlock), 		// Locked transfer
    .HREADYS5(macb3_hready),  	// Transfer done

    // CPU slave signals to busmatrix
    .HRDATAM0(cpu_tcm_hrdata),     	// Read data bus
    .HREADYOUTM0(cpu_tcm_hready),   	// HREADY feedback
    .HRESPM0(cpu_tcm_hresp), 		// Transfer response
    
    // SRAM slave signals to busmatrix
    .HRDATAM1(sram_subsystem_hrdata),  	// Read data bus
    .HREADYOUTM1(sram_subsystem_hready),   	// HREADY feedback
    .HRESPM1(sram_subsystem_hresp),    	// Transfer response
    
    // ROM slave signals to busmatrix
    .HRDATAM2(rom_subsystem_hrdata),  	// Read data bus
    .HREADYOUTM2(rom_subsystem_hready),	// HREADY feedback
    .HRESPM2(rom_subsystem_hresp),      // Transfer response

    // AHB2APB0 slave signals to busmatrix
    .HRDATAM3   (ahb2apb0_hrdata),     	// Read data bus
    .HREADYOUTM3(ahb2apb0_hready),   	// HREADY feedback
    .HRESPM3    (ahb2apb0_hresp ),      	// Transfer response
    
    // SMC slave signals to busmatrix
    .HRDATAM4(smc_hrdata),     		// Read data bus
    .HREADYOUTM4(smc_hready),   	// HREADY feedback
    .HRESPM4(smc_hresp),      		// Transfer response
    
    // DMA slave signals to busmatrix
    .HRDATAM5   (dma_s_hrdata),     	// Read data bus
    .HREADYOUTM5(dma_s_hready),   	// HREADY feedback
    .HRESPM5    (dma_s_hresp),      	// Transfer response

    // AHB2APB1 slave signals to busmatrix
    .HRDATAM6   (ahb2apb1_hrdata),     	// Read data bus
    .HREADYOUTM6(ahb2apb1_hready),   	// HREADY feedback
    .HRESPM6    (ahb2apb1_hresp ),      	// Transfer response
    
    // Unused
    .HRDATAM7(32'b0),  	// Read data bus
    .HREADYOUTM7(1'b1),   	// HREADY feedback
    .HRESPM7(2'b0),    	// Transfer response
    
    // OCP
    .HRDATAM8(ahb2ocp_hrdata),  	// Read data bus
    .HREADYOUTM8(ahb2ocp_hready),   	// HREADY feedback
    .HRESPM8(ahb2ocp_hresp),    	// Transfer response
    
    // Scan test dummy signals; not connected until scan insertion 
    .SCANENABLE(scan_mode),   		// Scan Test Mode Enable
    .SCANINHCLK(hclk),   		// Scan Chain Input
    
    // CPU slave signals from busmatrix
    .HSELM0(cpu_tcm_hsel),       	// Slave Select
    .HADDRM0(cpu_tcm_haddr),      	// Address bus
    .HTRANSM0(cpu_tcm_htrans_raw),     	// Transfer type 
    .HWRITEM0(cpu_tcm_hwrite),     	// Transfer direction
    .HSIZEM0(cpu_tcm_hsize),      	// Transfer size
    .HBURSTM0(cpu_tcm_hburst),     	// Burst type
    .HPROTM0(cpu_tcm_hprot),      	// Protection control
    .HMASTERM0(cpu_tcm_hmaster),    	// Master select
    .HWDATAM0(cpu_tcm_hwdata),     	// Write data
    .HMASTLOCKM0(cpu_tcm_hmastlock),   // Locked transfer
    .HREADYMUXM0(cpu_tcm_hready_in),  	// Transfer done
    
    // SRAM slave signals from busmatrix
    .HSELM1(sram_subsystem_hsel),       	// Slave Select
    .HADDRM1(sram_subsystem_haddr),      	// Address bus
    .HTRANSM1(sram_subsystem_htrans_raw),     	// Transfer type 
    .HWRITEM1(sram_subsystem_hwrite),     	// Transfer direction
    .HSIZEM1(sram_subsystem_hsize),      	// Transfer size
    .HBURSTM1(sram_subsystem_hburst),     // Burst type
    .HPROTM1(sram_subsystem_hprot),      // Protection control
    .HMASTERM1(sram_subsystem_hmaster),    // Master select
    .HWDATAM1(sram_subsystem_hwdata),     	// Write data
    .HMASTLOCKM1(sram_subsystem_hmastlock),  // Locked transfer
    .HREADYMUXM1(sram_subsystem_hready_in),  	// Transfer done
    
    // ROM slave signals from busmatrix
    .HSELM2(rom_subsystem_hsel),       		// Slave Select
    .HADDRM2(rom_subsystem_haddr),      	// Address bus
    .HTRANSM2(rom_subsystem_htrans_raw),     	// Transfer type 
    .HWRITEM2(rom_subsystem_hwrite),     	// Transfer direction
    .HSIZEM2(rom_subsystem_hsize),      	// Transfer size
    .HBURSTM2(rom_subsystem_hburst),     // Burst type
    .HPROTM2(rom_subsystem_hprot),      // Protection control
    .HMASTERM2(rom_subsystem_hmaster),    // Master select
    .HWDATAM2(rom_subsystem_hwdata),     // Write data
    .HMASTLOCKM2(rom_subsystem_hmastlock),  // Locked transfer
    .HREADYMUXM2(rom_subsystem_hready_in),  	// Transfer done
    
    // AHB2APB0 slave signals from busmatrix
    .HSELM3(ahb2apb0_hsel),       		// Slave Select
    .HADDRM3(ahb2apb0_haddr),      		// Address bus
    .HTRANSM3(ahb2apb0_htrans_raw),     		// Transfer type 
    .HWRITEM3(ahb2apb0_hwrite),     		// Transfer direction
    .HSIZEM3(ahb2apb0_hsize),      		// Transfer size
    .HBURSTM3(ahb2apb0_hburst),     // Burst type
    .HPROTM3(ahb2apb0_hprot),      // Protection control
    .HMASTERM3(ahb2apb0_hmaster),    // Master select
    .HWDATAM3(ahb2apb0_hwdata),     		// Write data
    .HMASTLOCKM3(ahb2apb0_hmastlock),  // Locked transfer
    .HREADYMUXM3(ahb2apb0_hready_in),  		// Transfer done
    
    // SMC slave signals from busmatrix
    .HSELM4(smc_hsel),       			// Slave Select
    .HADDRM4(smc_haddr),      			// Address bus
    .HTRANSM4(smc_htrans_raw),     			// Transfer type 
    .HWRITEM4(smc_hwrite),     			// Transfer direction
    .HSIZEM4(smc_hsize),      			// Transfer size
    .HBURSTM4(smc_hburst),     // Burst type
    .HPROTM4(smc_hprot),      // Protection control
    .HMASTERM4(smc_hmaster),    // Master select
    .HWDATAM4(smc_hwdata),     			// Write data
    .HMASTLOCKM4(smc_hmastlock),  // Locked transfer
    .HREADYMUXM4(smc_hready_in),  		// Transfer done
    
    // DMA slave signals from busmatrix
    .HSELM5(dma_s_hsel),      			// Slave Select
    .HADDRM5(dma_s_haddr), 			// Address bus
    .HTRANSM5(dma_s_htrans_raw),    		// Transfer type 
    .HWRITEM5(dma_s_hwrite),    		// Transfer direction
    .HSIZEM5(dma_s_hsize),     			// Transfer size
    .HBURSTM5(dma_s_hburst),    // Burst type
    .HPROTM5(dma_s_hprot),     // Protection control
    .HMASTERM5(dma_s_hmaster),   // Master select
    .HWDATAM5(dma_s_hwdata), 			// Write data
    .HMASTLOCKM5(dma_s_hmastlock), // Locked transfer
    .HREADYMUXM5(dma_s_hready_in), 		// Transfer done
 
    // AHB2APB1 slave signals from busmatrix
    .HSELM6(ahb2apb1_hsel),       		// Slave Select
    .HADDRM6(ahb2apb1_haddr),      		// Address bus
    .HTRANSM6(ahb2apb1_htrans_raw),     		// Transfer type 
    .HWRITEM6(ahb2apb1_hwrite),     		// Transfer direction
    .HSIZEM6(ahb2apb1_hsize),      		// Transfer size
    .HBURSTM6(ahb2apb1_hburst),     // Burst type
    .HPROTM6(ahb2apb1_hprot),      // Protection control
    .HMASTERM6(ahb2apb1_hmaster),    // Master select
    .HWDATAM6(ahb2apb1_hwdata),     		// Write data
    .HMASTLOCKM6(ahb2apb1_hmastlock),  // Locked transfer
    .HREADYMUXM6(ahb2apb1_hready_in),  		// Transfer done

     // Unused
    .HSELM7(),       	// Slave Select
    .HADDRM7(),      	// Address bus
    .HTRANSM7(),     	// Transfer type 
    .HWRITEM7(),     	// Transfer direction
    .HSIZEM7(),      	// Transfer size
    .HBURSTM7(),     // Burst type
    .HPROTM7(),      // Protection control
    .HMASTERM7(),    // Master select
    .HWDATAM7(),     	// Write data
    .HMASTLOCKM7(),  // Locked transfer
    .HREADYMUXM7(),  	// Transfer done
    
    // OCP
    .HSELM8(ahb2ocp_hsel),       	// Slave Select
    .HADDRM8(ahb2ocp_haddr),      	// Address bus
    .HTRANSM8(ahb2ocp_htrans_raw),     	// Transfer type 
    .HWRITEM8(ahb2ocp_hwrite),     	// Transfer direction
    .HSIZEM8(ahb2ocp_hsize),      	// Transfer size
    .HBURSTM8(ahb2ocp_hburst),     // Burst type
    .HPROTM8(ahb2ocp_hprot),      // Protection control
    .HMASTERM8(ahb2ocp_hmaster),    // Master select
    .HWDATAM8(ahb2ocp_hwdata),     	// Write data
    .HMASTLOCKM8(ahb2ocp_hmastlock),  // Locked transfer
    .HREADYMUXM8(ahb2ocp_hready_in),  	// Transfer done
    

    // DMA master signals from busmatrix
    .HRDATAS0   (dma_m_hrdata),     // Read data bus
    .HREADYOUTS0(dma_m_hready),     // HREADY feedback
    .HRESPS0    (dma_m_hresp),     // Transfer response
    
    // CPU master signals from busmatrix
    .HRDATAS1(cpu_biu_hrdata),     // Read data bus
    .HREADYOUTS1(cpu_biu_hready),  //    HREADY feedback
    .HRESPS1(cpu_biu_hresp),      // Transfer response
    
    // MACB0 master signals from busmatrix
    .HRDATAS2   (macb0_hrdata),     // Read data bus
    .HREADYOUTS2(macb0_hready),     // HREADY feedback
    .HRESPS2    (macb0_hresp),     // Transfer response
    
    // MACB1 master signals from busmatrix
    .HRDATAS3   (macb1_hrdata),     // Read data bus
    .HREADYOUTS3(macb1_hready),     // HREADY feedback
    .HRESPS3    (macb1_hresp),     // Transfer response
    
    // MACB2 master signals from busmatrix
    .HRDATAS4   (macb2_hrdata),     // Read data bus
    .HREADYOUTS4(macb2_hready),     // HREADY feedback
    .HRESPS4    (macb2_hresp),     // Transfer response
    
    // MACB3 master signals from busmatrix
    .HRDATAS5   (macb3_hrdata),     // Read data bus
    .HREADYOUTS5(macb3_hready),     // HREADY feedback
    .HRESPS5    (macb3_hresp),     // Transfer response
    
    // Scan test dummy signals; not connected until scan insertion 
    .SCANOUTHCLK()  // Scan Chain Output
);


`ifdef FV_KIT_OR1K

`include "or1200_defines.v"  

wire or1k_rst;
wire [`OR1200_PIC_INTS-1:0] or1k_ints;
wire [1:0] or1k_clmode;

wire or1k_dbg_stall;	
wire or1k_dbg_ewt;	
wire or1k_dbg_stb;   
wire or1k_dbg_we;    
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_dbg_adr;	
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_dbg_dat;	

`ifdef OR1200_BIST
wire or1k_mbist_si;
wire [`OR1200_MBIST_CTRL_WIDTH - 1:0] or1k_mbist_ctrl;
`endif

wire or1k_pm_cpustall;

wire or1k_iwb_ack; 
wire or1k_iwb_err; 
wire or1k_iwb_rty; 
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_iwb_dat_i;
wire or1k_iwb_cyc; 
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_iwb_adr; 
wire or1k_iwb_stb; 
wire or1k_iwb_we; 
wire [3:0] or1k_iwb_sel; 
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_iwb_dat_o;
wire or1k_dwb_ack; 
wire or1k_dwb_err; 
wire or1k_dwb_rty; 
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_dwb_dat_i;
wire or1k_dwb_cyc; 
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_dwb_adr; 
wire or1k_dwb_stb; 
wire or1k_dwb_we; 
wire [3:0] or1k_dwb_sel; 
wire [`OR1200_OPERAND_WIDTH-1:0] or1k_dwb_dat_o;

// tie offs
assign or1k_clmode = 'b00; // WB clk = CPU clk
assign or1k_dbg_stall = 'b0;	
assign or1k_dbg_ewt = 'b0;	
assign or1k_dbg_stb = 'b0;   
assign or1k_dbg_we = 'b0;    
assign or1k_dbg_adr = 'b0;	
assign or1k_dbg_dat = 'b0;	

`ifdef OR1200_BIST
assign or1k_mbist_si = 'b0;
assign or1k_mbist_ctrl = 'b0;
`endif

assign or1k_pm_cpustall = 'b0;
assign or1k_iwb_err = 'b0;
assign or1k_iwb_rty = 'b0;
assign or1k_dwb_err = 'b0;
assign or1k_dwb_rty = 'b0;

assign or1k_rst = ~n_hreset;

// FIQ is non-maskable, IRQ is maskable.
// Note: the lower 2 interrupts on OR1200 are non-maskable.
wire pcm_irq;
wire [2:0] ttc_irq;
wire gpio_irq;
wire uart0_irq;
wire uart1_irq;
wire spi_irq;
assign or1k_ints = {16'b0, 
  macb0_int,
  macb1_int,
  macb2_int,
  macb3_int,
  pcm_irq,
  1'b0,
  ttc_irq[2],
  ttc_irq[1],
  ttc_irq[0],
  gpio_irq, 
  uart1_irq, 
  uart0_irq, 
  spi_irq, 
  dma_irq, 
  1'b0, 1'b0};

// OR1200 CPU
or1200_top i_or1200 (
	// System
	.clk_i(hclk), 
        .rst_i(or1k_rst), 
        .pic_ints_i(or1k_ints), 
        .clmode_i(or1k_clmode),

	// Instruction WISHBONE INTERFACE
	.iwb_clk_i(hclk),
        .iwb_rst_i(or1k_rst), 
        .iwb_ack_i(or1k_iwb_ack), 
        .iwb_err_i(or1k_iwb_err), 
        .iwb_rty_i(or1k_iwb_rty), 
        .iwb_dat_i(or1k_iwb_dat_i),
	.iwb_cyc_o(or1k_iwb_cyc), 
        .iwb_adr_o(or1k_iwb_adr), 
        .iwb_stb_o(or1k_iwb_stb), 
        .iwb_we_o(or1k_iwb_we), 
        .iwb_sel_o(or1k_iwb_sel), 
        .iwb_dat_o(or1k_iwb_dat_o),
`ifdef OR1200_WB_CAB
	//.iwb_cab_o,
        Unsupported!
`endif
`ifdef OR1200_WB_B3
	//.iwb_cti_o, 
        //.iwb_bte_o,
        Unsupported!
`endif
	// Data WISHBONE INTERFACE
	.dwb_clk_i(hclk), 
        .dwb_rst_i(or1k_rst), 
        .dwb_ack_i(or1k_dwb_ack), 
        .dwb_err_i(or1k_dwb_err), 
        .dwb_rty_i(or1k_dwb_rty), 
        .dwb_dat_i(or1k_dwb_dat_i),
	.dwb_cyc_o(or1k_dwb_cyc), 
        .dwb_adr_o(or1k_dwb_adr), 
        .dwb_stb_o(or1k_dwb_stb), 
        .dwb_we_o(or1k_dwb_we), 
        .dwb_sel_o(or1k_dwb_sel), 
        .dwb_dat_o(or1k_dwb_dat_o),
`ifdef OR1200_WB_CAB
	//.dwb_cab_o,
        Unsupported!  
`endif
`ifdef OR1200_WB_B3
	//.dwb_cti_o, 
        //.dwb_bte_o,
        Unsupported!
`endif

	// External Debug Interface
	.dbg_stall_i(or1k_dbg_stall), 
        .dbg_ewt_i(or1k_dbg_ewt),	
        .dbg_lss_o(), 
        .dbg_is_o(), 
        .dbg_wp_o(), 
        .dbg_bp_o(),
	.dbg_stb_i(or1k_dbg_stb), 
        .dbg_we_i(or1k_dbg_we), 
        .dbg_adr_i(or1k_dbg_adr), 
        .dbg_dat_i(or1k_dbg_dat), 
        .dbg_dat_o(), 
        .dbg_ack_o(),
	
`ifdef OR1200_BIST
	// RAM BIST
	.mbist_si_i(or1k_mbist_si), 
        .mbist_so_o(), 
        .mbist_ctrl_i(or1k_mbist_ctrl),
`endif
	// Power Management
	.pm_cpustall_i(or1k_pm_cpustall),
	.pm_clksd_o(), 
        .pm_dc_gate_o(), 
        .pm_ic_gate_o(), 
        .pm_dmmu_gate_o(), 
	.pm_immu_gate_o(), 
        .pm_tt_gate_o(), 
        .pm_cpu_gate_o(), 
        .pm_wakeup_o(), 
        .pm_lvolt_o()
  
);

wire [31:0] or1k_d_haddr;
wire [1:0]  or1k_d_htrans;
wire        or1k_d_hwrite;
wire [2:0]  or1k_d_hsize;
wire [2:0]  or1k_d_hburst;
wire [31:0] or1k_d_hwdata;
wire [31:0] or1k_d_hrdata;
wire        or1k_d_hready;
wire [1:0]  or1k_d_hresp;

assign cpu_biu_haddr   = or1k_d_haddr;  
assign cpu_biu_htrans  = or1k_d_htrans;
assign cpu_biu_hwrite  = or1k_d_hwrite;
assign cpu_biu_hsize   = or1k_d_hsize;  
assign cpu_biu_hburst  = or1k_d_hburst; 
assign cpu_biu_hprot   = 'b1;  // Data access
assign cpu_biu_hwdata  = or1k_d_hwdata;
assign cpu_biu_hlock   = 'b0; 
assign or1k_d_hrdata   = cpu_biu_hrdata;
assign or1k_d_hready   = cpu_biu_hready;   
assign or1k_d_hresp    = cpu_biu_hresp; 

// OR1k Data WB to AHB bridge
wb2ahb i_dwb_to_ahb (
  // Wishbone ports from WB master
  .clk_i(hclk),
  .rst_i(or1k_rst),
  .cyc_i(or1k_dwb_cyc),
  .stb_i(or1k_dwb_stb),
  .sel_i(or1k_dwb_sel),
  .we_i(or1k_dwb_we),
  .addr_i(or1k_dwb_adr),
  .data_i(or1k_dwb_dat_o),
  .data_o(or1k_dwb_dat_i),
  .ack_o(or1k_dwb_ack),

  // AHB ports to AHB slave
  .hclk(hclk),
  .hreset_n(n_hreset),
  .htrans(or1k_d_htrans),
  .hsize(or1k_d_hsize),
  .hburst(or1k_d_hburst),
  .hwrite(or1k_d_hwrite),
  .haddr(or1k_d_haddr),
  .hwdata(or1k_d_hwdata),
  .hrdata(or1k_d_hrdata),
  .hready(or1k_d_hready),
  .hresp(or1k_d_hresp)
);

wire        or1k_i_hsel;
wire [31:0] or1k_i_haddr;
wire [1:0]  or1k_i_htrans;
wire        or1k_i_hwrite;
wire [2:0]  or1k_i_hsize;
wire [2:0]  or1k_i_hburst;
wire [31:0] or1k_i_hwdata;
wire [31:0] or1k_i_hrdata;
wire        or1k_i_hready;
wire        or1k_i_hready_in;
wire [1:0]  or1k_i_hresp;
wire [3:0]  or1k_i_hprot;
wire [3:0]  or1k_i_hmaster;
wire        or1k_i_hmastlock;

assign or1k_i_hsel  = 'b1;
assign or1k_i_hprot = 'b0; // Opcode fetch
assign or1k_i_hmaster = 'b0;
assign or1k_i_hmastlock = 'b0;
assign or1k_i_hready_in = 'b1;

// OR1k Instruction WB to AHB bridge
wb2ahb i_iwb_to_ahb (
  // Wishbone ports from WB master
  .clk_i(hclk),
  .rst_i(or1k_rst),
  .cyc_i(or1k_iwb_cyc),
  .stb_i(or1k_iwb_stb),
  .sel_i(or1k_iwb_sel),
  .we_i(or1k_iwb_we),
  .addr_i(or1k_iwb_adr),
  .data_i(or1k_iwb_dat_o),
  .data_o(or1k_iwb_dat_i),
  .ack_o(or1k_iwb_ack),

  // AHB ports to AHB slave
  .hclk(hclk),
  .hreset_n(n_hreset),
  .htrans(or1k_i_htrans),
  .hsize(or1k_i_hsize),
  .hburst(or1k_i_hburst),
  .hwrite(or1k_i_hwrite),
  .haddr(or1k_i_haddr),
  .hwdata(or1k_i_hwdata),
  .hrdata(or1k_i_hrdata),
  .hready(or1k_i_hready),
  .hresp(or1k_i_hresp)
);

// Instruction SRAM
insn_sram_subsystem i_instruction_sram(
    //inputs
    .hclk(hclk),         
    .n_hreset(n_hreset),      

    // AHB interface
    .hsel(or1k_i_hsel),         
    .haddr(or1k_i_haddr),        
    .htrans(or1k_i_htrans),       
    .hsize(or1k_i_hsize),        
    .hwrite(or1k_i_hwrite),       
    .hwdata(or1k_i_hwdata),       
    .hready_in(or1k_i_hready_in),    
    .hburst(or1k_i_hburst),        
    .hprot(or1k_i_hprot),         
    .hmaster(or1k_i_hmaster),       
    .hmastlock(or1k_i_hmastlock),     
    
     // Scan inputs
    .scan_mode(scan_mode),    

     // Outputs
     // AHB interface
    .hrdata(or1k_i_hrdata),       
    .hready(or1k_i_hready),       
    .hresp(or1k_i_hresp)         
);

`endif // FV_KIT_OR1K

`ifdef FV_KIT_ARM

arm_subsystem i_arm_subsystem (
      .scan_mode(scan_mode),
      
		.HRESETn(n_hreset), 
		.HRDATA(cpu_biu_hrdata), 
		.HREADY(cpu_biu_hready), 
		.HRESP(cpu_biu_hresp), 
		.HADDR(cpu_biu_haddr),
		.HTRANS(cpu_biu_htrans), 
		.HWRITE(cpu_biu_hwrite), 
		.HSIZE(cpu_biu_hsize), 
		.HBURST(cpu_biu_hburst), 
		.HPROT(cpu_biu_hprot), 
		.HWDATA(cpu_biu_hwdata),
		.HMASTLOCK(cpu_biu_hlock), 
		.HWDATAD(cpu_tcm_hwdata), 
		.HSELD(cpu_tcm_hsel), 
		.HADDRD(cpu_tcm_haddr),
		.HTRANSD(cpu_tcm_htrans), 
		.HBURSTD(cpu_tcm_hburst),
		.HWRITED(cpu_tcm_hwrite), 
		.HSIZED(cpu_tcm_hsize), 
		.HPROTD(cpu_tcm_hprot), 
		.HREADYIND(cpu_tcm_hready_in),
		.HRDATAD(cpu_tcm_hrdata), 
		.HREADYOUTD(cpu_tcm_hready), 
		.HRESPD(cpu_tcm_hresp), 

		.nFIQ(arm_nfiq), 
		.nIRQ(arm_nirq), 

      .COMMRX(), 
		.COMMTX(), 
		.DBGACK(), 
		.DBGEN(tie_lo_1bit),
 		.DBGRQI(),
 		.EDBGRQ(tie_lo_1bit), 
		.DBGEXT(tie_lo_2bit), 
		.DBGINSTREXEC(),
      .HCLKEND(tie_hi_1bit),
      .DBGnTRST(tie_lo_1bit), 
		.DBGTCKEN(tie_lo_1bit), 
		.DBGTDI(tie_hi_1bit), 
		.DBGTMS(tie_hi_1bit), 
		.DBGTDO(), 				// Unused TDO
		.DBGIR(), 
		.DBGSCREG(), 
		.DBGTAPSM(),
      .DBGnTDOEN(), 
		.DBGSDIN(), 
		.DBGSDOUT(tie_lo_1bit), 
		.CLK(hclk), 
		.HCLKEN(tie_hi_1bit),   
		.BIGENDOUT(), 
		.VINITHI(tie_hi_1bit), 
		.INITRAM(tie_hi_1bit),
      .TAPID(tie_lo_32bit), 
		.SE(tie_lo_1bit), 
		.WEXTEST(tie_lo_1bit), 
		.STANDBYWFI()
);

`endif // FV_KIT_ARM

dma i_dma(
            .hclk(hclk),                       // ahb system clock
            .n_hreset(n_hreset),               // ahb system reset
            // ahb interface slave signals 
            .dma_hready(dma_s_hready),                 // hready output from slave
            .dma_hresp(dma_s_hresp),                  // hresp output from slave
            .haddr(dma_s_haddr),                      // input from master
            .hsel(dma_s_hsel),                       // input from master 
            .htrans(dma_s_htrans),                     // input from master
            .hwrite(dma_s_hwrite),                     // input from master                
            .hsize(dma_s_hsize),                      // input from master
            .hburst(dma_s_hburst),    // Burst type
            .hprot(dma_s_hprot),     // Protection control
            .hmaster(dma_s_hmaster),   // Master select
            .hmastlock(dma_s_hmastlock), // Locked transfer
            .hready_in(dma_s_hready_in),      // Transfer done
            .hwdata(dma_s_hwdata),                     // input from master
            .dma_hrdata(dma_s_hrdata),                 // data output from slave
            // ahb interface master signals
            .hrdata_dma(dma_m_hrdata),                 //
            .hready_dma(dma_m_hready),
            .hresp_dma(dma_m_hresp),
            .hgrant(tie_hi_1bit),
            .dma_haddr(dma_m_haddr),
            .dma_htrans(dma_m_htrans),
            .dma_hwrite(dma_m_hwrite),
            .dma_hsize(dma_m_hsize),
            .dma_hburst(dma_m_hburst),
            .dma_hprot(dma_m_hprot),
            .dma_hwdata(dma_m_hwdata),
            .dma_hbusreq(),
            .dma_hlock(dma_m_hlock),
            // apb interface master signals
            //pclk,
            //presetn,
            .apb_request(),
            .dma_penable(),
            .dma_pwrite(),
            .dma_paddr(),
            .dma_pwdata(),
            .prdata(tie_lo_16bit),
            .pready(tie_lo_1bit),
            // channel control lines
            .data_av0(tie_lo_1bit),
            .slot_av0(tie_lo_1bit),
            .word_av0(tie_lo_1bit),
            .data_av1(tie_lo_1bit),
            .slot_av1(tie_lo_1bit),
            .word_av1(tie_lo_1bit),
            .data_av2(tie_lo_1bit),
            .slot_av2(tie_lo_1bit),
            .word_av2(tie_lo_1bit),
            .byte_access(),
            .double_clk(tie_lo_1bit),
            .dma_int(dma_irq),
	         //scan signals
            .scan_en(tie_lo_1bit),      // Scan enable pin
            .scan_in(tie_lo_1bit),    // Scan input for first chain
	         .scan_out()
            );

sram_subsystem i_sram_subsystem(

         //inputs
    	.hclk(hclk),         // AHB Clock
    	.n_hreset(n_hreset),      // AHB reset - Active low
         // AHB interface
    	.hsel(sram_subsystem_hsel),         // AHB2APB select
    	.haddr(sram_subsystem_haddr),        // Address bus
    	.htrans(sram_subsystem_htrans),       // Transfer type
    	.hsize(sram_subsystem_hsize),        // AHB Access type - byte, half-word, word
    	.hwrite(sram_subsystem_hwrite),       // Write signal
    	.hwdata(sram_subsystem_hwdata),       // Write data
        .hready_in(sram_subsystem_hready_in),    // Combined hready across all slaves
        .hburst(sram_subsystem_hburst),        // hburst signal
        .hprot(sram_subsystem_hprot),         // hprot signal
        .hmaster(sram_subsystem_hmaster),       // hmaster signal
        .hmastlock(sram_subsystem_hmastlock),     // master lock signal
    
         // Scan inputs
    	.scan_mode(scan_mode),    // test mode
      .clk_SRPG_macb0_en(clk_SRPG_macb0_en),
      .clk_SRPG_macb1_en(clk_SRPG_macb1_en),
      .clk_SRPG_macb2_en(clk_SRPG_macb2_en),
      .clk_SRPG_macb3_en(clk_SRPG_macb3_en),

    		// Outputs
         // AHB inter.face
    	.hrdata(sram_subsystem_hrdata),       // Read data provided from target slave
    	.hready(sram_subsystem_hready),       // Ready for new bus cycle from target slave
    	.hresp(sram_subsystem_hresp)         // Response from the bridge
);

rom_subsystem i_rom_subsystem(
	      //Inputs
    		.hclk(hclk),         // AHB Clock
    		.n_hreset(n_hreset),      // AHB reset - Active low
    		// AHB interface
    		.hsel(rom_subsystem_hsel),         // AHB2APB select
    		.haddr(rom_subsystem_haddr),        // Address bus
    		.htrans(rom_subsystem_htrans),       // Transfer type
    		.hsize(rom_subsystem_hsize),        // AHB Access type - byte, half-word, word
    		.hwrite(rom_subsystem_hwrite),       // Write signal
         .hwdata(rom_subsystem_hwdata),
         .hready_in(rom_subsystem_hready_in),    // Combined hready across all slaves
         .hburst(rom_subsystem_hburst),     // Burst type
         .hprot(rom_subsystem_hprot),      // Protection control
         .hmaster(rom_subsystem_hmaster),    // Master select
         .hmastlock(rom_subsystem_hmastlock),  // Locked transfer
         
    		// Scan inputs
    		.scan_mode(scan_mode),      	// test mode selection

    	   // Outputs
    		// AHB interface
    		.hrdata(rom_subsystem_hrdata),       // Read data provided from target slave
    		.hready(rom_subsystem_hready),       // Ready for new bus cycle from target slave
    		.hresp(rom_subsystem_hresp)         // Response from the bridge
);

apb_subsystem_0  i_apb_subsystem(
    // AHB interface
    .hclk(hclk),
    .n_hreset(n_hreset),
    .hsel(ahb2apb0_hsel),
    .haddr(ahb2apb0_haddr),
    .htrans(ahb2apb0_htrans),
    .hsize(ahb2apb0_hsize),
    .hwrite(ahb2apb0_hwrite),
    .hwdata(ahb2apb0_hwdata),
    .hready_in(ahb2apb0_hready_in),
    .hburst(ahb2apb0_hburst),
    .hprot(ahb2apb0_hprot),
    .hmaster(ahb2apb0_hmaster),
    .hmastlock(ahb2apb0_hmastlock),
    .hrdata(hrdata_apb0),
    .hready(hready_apb0),
    .hresp(hresp_apb0),
    
    // APB system interface
    .pclk(pclk),
    .n_preset(n_preset),
    
    //SPI ports
    .n_ss_in(n_ss_in),
    .mi(mi),
    .si(si),
    .sclk_in(sclk_in),
    .so(so),
    .mo(mo),
    .sclk_out(sclk_out),
    .n_ss_out(n_ss_out),
    .n_so_en(n_so_en),
    .n_mo_en(n_mo_en),
    .n_sclk_en(n_sclk_en),
    .n_ss_en(n_ss_en),
    
    //UART0 ports
    .ua_rxd(ua_rxd),
    .ua_ncts(ua_ncts),
    .ua_txd(ua_txd),
    .ua_nrts(ua_nrts),
    
    //UART1 ports
    .ua_rxd1(ua_rxd1),
    .ua_ncts1(ua_ncts1),
    .ua_txd1(ua_txd1),
    .ua_nrts1(ua_nrts1),
    
    //GPIO ports
    .gpio_pin_in(gpio_pin_in),
    .n_gpio_pin_oe(n_gpio_pin_oe),
    .gpio_pin_out(gpio_pin_out),
    
    
    // SMC ports
    .smc_hclk(smc_hclk),
    .smc_n_hclk(smc_n_hclk),
    .smc_haddr(smc_haddr),
    .smc_htrans(smc_htrans),
    .smc_hsel(smc_hsel),
    .smc_hwrite(smc_hwrite),
    .smc_hsize(smc_hsize),
    .smc_hwdata(smc_hwdata),
    .smc_hready_in(smc_hready_in),
    .smc_hburst(smc_hburst),
    .smc_hprot(smc_hprot),
    .smc_hmaster(smc_hmaster),
    .smc_hmastlock(smc_hmastlock),
    .smc_hrdata(smc_hrdata), 
    .smc_hready(smc_hready),
    .smc_hresp(smc_hresp),
    .smc_n_ext_oe(smc_n_ext_oe),
    .smc_data(smc_data),
    .smc_addr(smc_addr),
    .smc_n_be(smc_n_be),
    .smc_n_cs(smc_n_cs), 
    .smc_n_we(smc_n_we),
    .smc_n_wr(smc_n_wr),
    .smc_n_rd(smc_n_rd),
    .data_smc(data_smc),
    
    // PMC ports
    .clk_SRPG_macb0_en(clk_SRPG_macb0_en),
    .clk_SRPG_macb1_en(clk_SRPG_macb1_en),
    .clk_SRPG_macb2_en(clk_SRPG_macb2_en),
    .clk_SRPG_macb3_en(clk_SRPG_macb3_en),
    .core06v(core06v),
    .core08v(core08v),
    .core10v(core10v),
    .core12v(core12v),
    .macb3_wakeup(macb3_wakeup),
    .macb2_wakeup(macb2_wakeup),
    .macb1_wakeup(macb1_wakeup),
    .macb0_wakeup(macb0_wakeup),
    
    
    // Peripheral interrupts
    .pcm_irq(pcm_irq),
    .ttc_irq(ttc_irq),
    .gpio_irq(gpio_irq),
    .uart0_irq(uart0_irq),
    .uart1_irq(uart1_irq),
    .spi_irq(spi_irq),
    .DMA_irq(dma_irq),
    .macb0_int(macb0_int),
    .macb1_int(macb1_int),
    .macb2_int(macb2_int),
    .macb3_int(macb3_int),
    
    // Scan ports
    .scan_en(tie_lo_1bit),
    .scan_in_1(tie_lo_1bit),
    .scan_in_2(tie_lo_1bit),
    .scan_mode(scan_mode),
    .scan_out_1(),
    .scan_out_2()
);

apb_subsystem_1  i_apb_subsystem_1(
    // AHB interface
    .hclk(hclk),
    .n_hreset(n_hreset),
    .hsel(ahb2apb1_hsel),
    .haddr(ahb2apb1_haddr),
    .htrans(ahb2apb1_htrans),
    .hsize(ahb2apb1_hsize),
    .hwrite(ahb2apb1_hwrite),
    .hwdata(ahb2apb1_hwdata),
    .hready_in(ahb2apb1_hready_in),
    .hburst(ahb2apb1_hburst),
    .hprot(ahb2apb1_hprot),
    .hmaster(ahb2apb1_hmaster),
    .hmastlock(ahb2apb1_hmastlock),
    .hrdata(hrdata_apb1),
    .hready(hready_apb1),
    .hresp(hresp_apb1),
    
    // APB interface
    .pclk(pclk),       
    .n_preset(n_preset),  
    .paddr(apb1_paddr),
    .pwrite(apb1_pwrite),
    .penable(apb1_penable),
    .pwdata(apb1_pwdata), 
    
    // MAC0 APB ports
    .prdata_mac0(prdata_mac0),
    .psel_mac0(psel_mac0),
    .pready_mac0(pready_mac0),
    
    // MAC1 APB ports
    .prdata_mac1(prdata_mac1),
    .psel_mac1(psel_mac1),
    .pready_mac1(pready_mac1),
    
    // MAC2 APB ports
    .prdata_mac2(prdata_mac2),
    .psel_mac2(psel_mac2),
    .pready_mac2(pready_mac2),
    
    // MAC3 APB ports
    .prdata_mac3(prdata_mac3),
    .psel_mac3(psel_mac3),
    .pready_mac3(pready_mac3)
);


//--------------------------4 way Ethernet Switch----------------------------//
mac_veneer i_mac0_veneer (
   // PHY signals
   .col(macb0_col),
   .crs(macb0_crs),
   .tx_er(macb0_tx_er),
   .txd(macb0_txd),
   .tx_en(macb0_tx_en),
   .tx_clk(macb0_tx_clk),
   .rxd(macb0_rxd),
   .rx_er(macb0_rx_er),
   .rx_clk(macb0_rx_clk),
   .rx_dv(macb0_rx_dv),
   
   // MII signals
   .mdc(macb_mdc),
   .mdio_in(macb_mdio_in),
   .mdio_out(macb_mdio_out),
   .mdio_en(macb_mdio_en),
   
   // APB interface signals
   .pclk(pclk & clk_SRPG_macb0_en),
   .n_preset(n_preset),
   .paddr(apb1_paddr),
   .prdata(prdata_mac0),
   .pwdata(apb1_pwdata),
   .pwrite(apb1_pwrite),
   .penable(apb1_penable),
   .psel(psel_mac0),
   .pready(pready_mac0),

   // AHB interface signals
   .hclk(hclk & clk_SRPG_macb0_en),             
   .n_hreset(n_hreset),
   .hready(macb0_hready),
   .hresp(macb0_hresp),
   .hrdata(macb0_hrdata),
   .hlock(macb0_hlock),
   .haddr(macb0_haddr),
   .htrans(macb0_htrans),
   .hwrite(macb0_hwrite),
   .hsize(macb0_hsize),
   .hburst(macb0_hburst),
   .hprot(macb0_hprot),
   .hwdata(macb0_hwdata),
   .intr(macb0_int),
   .macb_wakeup(macb0_wakeup)
); 

mac_veneer i_mac1_veneer (
   // PHY signals
   .col(macb1_col),
   .crs(macb1_crs),
   .tx_er(macb1_tx_er),
   .txd(macb1_txd),
   .tx_en(macb1_tx_en),
   .tx_clk(macb1_tx_clk),
   .rxd(macb1_rxd),
   .rx_er(macb1_rx_er),
   .rx_clk(macb1_rx_clk),
   .rx_dv(macb1_rx_dv),
   
   // MII signals
   .mdc(),
   .mdio_in(),
   .mdio_out(),
   .mdio_en(),
   
   // APB interface signals
   .pclk(pclk & clk_SRPG_macb1_en),
   .n_preset(n_preset),
   .paddr(apb1_paddr),
   .prdata(prdata_mac1),
   .pwdata(apb1_pwdata),
   .pwrite(apb1_pwrite),
   .penable(apb1_penable),
   .psel(psel_mac1),
   .pready(pready_mac1),

   // AHB interface signals
   .hclk(hclk & clk_SRPG_macb1_en),             
   .n_hreset(n_hreset),
   .hready(macb1_hready),
   .hresp(macb1_hresp),
   .hrdata(macb1_hrdata),
   .hlock(macb1_hlock),
   .haddr(macb1_haddr),
   .htrans(macb1_htrans),
   .hwrite(macb1_hwrite),
   .hsize(macb1_hsize),
   .hburst(macb1_hburst),
   .hprot(macb1_hprot),
   .hwdata(macb1_hwdata),
   .intr(macb1_int),
   .macb_wakeup(macb1_wakeup)
); 

mac_veneer i_mac2_veneer (
   // PHY signals
   .col(macb2_col),
   .crs(macb2_crs),
   .tx_er(macb2_tx_er),
   .txd(macb2_txd),
   .tx_en(macb2_tx_en),
   .tx_clk(macb2_tx_clk),
   .rxd(macb2_rxd),
   .rx_er(macb2_rx_er),
   .rx_clk(macb2_rx_clk),
   .rx_dv(macb2_rx_dv),
   
   // MII signals
   .mdc(),
   .mdio_in(),
   .mdio_out(),
   .mdio_en(),
   
   // APB interface signals
   .pclk(pclk & clk_SRPG_macb2_en),
   .n_preset(n_preset),
   .paddr(apb1_paddr),
   .prdata(prdata_mac2),
   .pwdata(apb1_pwdata),
   .pwrite(apb1_pwrite),
   .penable(apb1_penable),
   .psel(psel_mac2),
   .pready(pready_mac2),

   // AHB interface signals
   .hclk(hclk & clk_SRPG_macb2_en),             
   .n_hreset(n_hreset),
   .hready(macb2_hready),
   .hresp(macb2_hresp),
   .hrdata(macb2_hrdata),
   .hlock(macb2_hlock),
   .haddr(macb2_haddr),
   .htrans(macb2_htrans),
   .hwrite(macb2_hwrite),
   .hsize(macb2_hsize),
   .hburst(macb2_hburst),
   .hprot(macb2_hprot),
   .hwdata(macb2_hwdata),
   .intr(macb2_int),
   .macb_wakeup(macb2_wakeup)
); 

mac_veneer i_mac3_veneer (
   // PHY signals
   .col(macb3_col),
   .crs(macb3_crs),
   .tx_er(macb3_tx_er),
   .txd(macb3_txd),
   .tx_en(macb3_tx_en),
   .tx_clk(macb3_tx_clk),
   .rxd(macb3_rxd),
   .rx_er(macb3_rx_er),
   .rx_clk(macb3_rx_clk),
   .rx_dv(macb3_rx_dv),
   
   // MII signals
   .mdc(),
   .mdio_in(),
   .mdio_out(),
   .mdio_en(),
   
   // APB interface signals
   .pclk(pclk & clk_SRPG_macb3_en),
   .n_preset(n_preset),
   .paddr(apb1_paddr),
   .prdata(prdata_mac3),
   .pwdata(apb1_pwdata),
   .pwrite(apb1_pwrite),
   .penable(apb1_penable),
   .psel(psel_mac3),
   .pready(pready_mac3),

   // AHB interface signals
   .hclk(hclk & clk_SRPG_macb3_en),             
   .n_hreset(n_hreset),
   .hready(macb3_hready),
   .hresp(macb3_hresp),
   .hrdata(macb3_hrdata),
   .hlock(macb3_hlock),
   .haddr(macb3_haddr),
   .htrans(macb3_htrans),
   .hwrite(macb3_hwrite),
   .hsize(macb3_hsize),
   .hburst(macb3_hburst),
   .hprot(macb3_hprot),
   .hwdata(macb3_hwdata),
   .intr(macb3_int),
   .macb_wakeup(macb3_wakeup)
); 

assign ahb2apb0_hrdata = hrdata_apb0;
assign ahb2apb0_hready = hready_apb0;
assign ahb2apb0_hresp  = hresp_apb0; 

assign ahb2apb1_hrdata = hrdata_apb1;
assign ahb2apb1_hready = hready_apb1;
assign ahb2apb1_hresp  = hresp_apb1; 

ahb2ocp i_ahb2ocp (


              .n_preset(n_hreset), 
              .pclk(hclk), 

// This is a APB interface provided to programm couple of registers withing OCP bridge. This is deactivated here and 
// registers will be loaded automatically at Reset
              .ao_psel_i(1'b0), 
              .ao_penable_i(1'b0), 
              .ao_pwrite_i(1'b0), 
              .ao_paddr_i(5'b0), 
              .ao_pwdata_i(32'b0),


              .hclk(hclk),
              .n_hreset(n_hreset),

              .ao_hsel_i(ahb2ocp_hsel),
	      .ao_haddr_i(ahb2ocp_haddr),
	      .ao_htrans_i(ahb2ocp_htrans),
	      .ao_hsize_i(ahb2ocp_hsize),
	      .ao_hburst_i(ahb2ocp_hburst),
	      .ao_hprot_i(ahb2ocp_hprot),
	      .ao_hwdata_i(ahb2ocp_hwdata),
	      .ao_hwrite_i(ahb2ocp_hwrite),
              .ao_hready_i(ahb2ocp_hready_in),

              .ao_sdata_i(ao_sdata_i),                // input from OCP i/f
              .ao_sresp_i(ao_sresp_i),                // input from OCP i/f
              .ao_sresplast_i(ao_sresplast_i),            // input from OCP i/f

              .ao_scmdaccept_i(ao_scmdaccept_i),           // input from OCP i/f
              .ao_sdataaccept_i(ao_sdataaccept_i),           // input from OCP i/f


              .ao_prdata_o(),           // Read data from APB i/f

	      .ao_hrdata_o(ahb2ocp_hrdata),
	      .ao_hready_o(ahb2ocp_hready),
	      .ao_hresp_o(ahb2ocp_hresp),

              .ao_mcmd_o(ao_mcmd_o),             // OCP output
              .ao_maddr_o(ao_maddr_o),             // OCP output
              .ao_matomic_length_o(ao_matomic_length_o),             // OCP output
              .ao_mburst_precise_o(ao_mburst_precise_o),             // OCP output
              .ao_mburst_single_req_o(ao_mburst_single_req_o),             // OCP output
              .ao_mburstlength_o(ao_mburstlength_o),             // OCP output
              .ao_mburst_seq_o(ao_mburst_seq_o),             // OCP output
              .ao_mtag_id_o(ao_mtag_id_o),             // OCP output
              .ao_mdata_tag_id_o(ao_mdata_tag_id_o),             // OCP output
              .ao_mdata_o(ao_mdata_o),             // OCP output
              .ao_mdatalast_o(ao_mdatalast_o),             // OCP output
              .ao_mdatavalid_o(ao_mdatavalid_o),             // OCP output
              .ao_mdataaccept_o(ao_mdataaccept_o),             // OCP output
              .ao_mrespaccept_o(ao_mrespaccept_o)             // OCP output
              );

endmodule
