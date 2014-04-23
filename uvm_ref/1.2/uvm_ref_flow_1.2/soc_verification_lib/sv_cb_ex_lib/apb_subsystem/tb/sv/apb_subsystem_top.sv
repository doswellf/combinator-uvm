/*-------------------------------------------------------------------------
File name   : apb_subsystem_top.v 
Title       : Top level file for the testbench 
Project     : APB Subsystem
Created     : March 2008
Description : This is top level file which instantiate the dut apb_subsyste,.v.
              It also has the assertion module which checks for the power down 
              and power up.To activate the assertion ifdef LP_ABV_ON is used.       
Notes       :
-------------------------------------------------------------------------*/ 
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

 `timescale 1ns/10ps


// Environment Constants
`ifndef AHB_DATA_WIDTH
  `define AHB_DATA_WIDTH          32              // AHB bus data width [32/64]
`endif
`ifndef AHB_ADDR_WIDTH
  `define AHB_ADDR_WIDTH          32              // AHB bus address width [32/64]
`endif
`ifndef AHB_DATA_MAX_BIT
  `define AHB_DATA_MAX_BIT        31              // MUST BE: AHB_DATA_WIDTH - 1
`endif
`ifndef AHB_ADDRESS_MAX_BIT
  `define AHB_ADDRESS_MAX_BIT     31              // MUST BE: AHB_ADDR_WIDTH - 1
`endif
`ifndef DEFAULT_HREADY_VALUE
  `define DEFAULT_HREADY_VALUE    1'b1            // Ready Asserted
`endif

`include "ahb_if.sv"
`include "apb_if.sv"
`include "apb_master_if.sv"
`include "apb_slave_if.sv"
`include "uart_if.sv"
`include "spi_if.sv"
`include "gpio_if.sv"
`include "coverage/uart_ctrl_internal_if.sv"

module apb_subsystem_top;
  import uvm_pkg::*;
  // Import the UVM Utilities Package

  import ahb_pkg::*;
  import apb_pkg::*;
  import uart_pkg::*;
  import gpio_pkg::*;
  import spi_pkg::*;
  import uart_ctrl_pkg::*;
  import apb_subsystem_pkg::*;

  `include "spi_reg_model.sv"
  `include "gpio_reg_model.sv"
  `include "apb_subsystem_reg_rdb.sv"
  `include "uart_ctrl_reg_seq_lib.sv"
  `include "spi_reg_seq_lib.sv"
  `include "gpio_reg_seq_lib.sv"

  //Include module UVC sequences
  `include "ahb_user_monitor.sv"
  `include "apb_subsystem_seq_lib.sv"
  `include "apb_subsystem_vir_sequencer.sv"
  `include "apb_subsystem_vir_seq_lib.sv"

  `include "apb_subsystem_tb.sv"
  `include "test_lib.sv"
   
  
   // ====================================
   // SHARED signals
   // ====================================
   
   // clock
   reg tb_hclk;
   
   // reset
   reg hresetn;
   
   // post-mux from master mux
   wire [`AHB_DATA_MAX_BIT:0] hwdata;
   wire [`AHB_ADDRESS_MAX_BIT:0] haddr;
   wire [1:0]  htrans;
   wire [2:0]  hburst;
   wire [2:0]  hsize;
   wire [3:0]  hprot;
   wire hwrite;

   // post-mux from slave mux
   wire        hready;
   wire [1:0]  hresp;
   wire [`AHB_DATA_MAX_BIT:0] hrdata;
  

  //  Specific signals of apb subsystem
  reg         ua_rxd;
  reg         ua_ncts;


  // uart outputs 
  wire        ua_txd;
  wire        us_nrts;

  wire   [7:0] n_ss_out;    // peripheral select lines from master
  wire   [31:0] hwdata_byte_alligned;

  reg [2:0] div8_clk;
 always @(posedge tb_hclk) begin
   if (!hresetn)
     div8_clk = 3'b000;
   else
     div8_clk = div8_clk + 1;
 end


  // Master virtual interface
  ahb_if ahbi_m0(.ahb_clock(tb_hclk), .ahb_resetn(hresetn));
  
  uart_if uart_s0(.clock(div8_clk[2]), .reset(hresetn));
  uart_if uart_s1(.clock(div8_clk[2]), .reset(hresetn));
  spi_if spi_s0();
  gpio_if gpio_s0();
  uart_ctrl_internal_if uart_int0(.clock(div8_clk[2]));
  uart_ctrl_internal_if uart_int1(.clock(div8_clk[2]));

  apb_if apbi_mo(.pclock(tb_hclk), .preset(hresetn));

  //M0
  assign ahbi_m0.AHB_HCLK = tb_hclk;
  assign ahbi_m0.AHB_HRESET = hresetn;
  assign ahbi_m0.AHB_HRESP = hresp;
  assign ahbi_m0.AHB_HRDATA = hrdata;
  assign ahbi_m0.AHB_HREADY = hready;

  assign apbi_mo.paddr = i_apb_subsystem.i_ahb2apb.paddr;
  assign apbi_mo.prwd = i_apb_subsystem.i_ahb2apb.pwrite;
  assign apbi_mo.pwdata = i_apb_subsystem.i_ahb2apb.pwdata;
  assign apbi_mo.penable = i_apb_subsystem.i_ahb2apb.penable;
  assign apbi_mo.psel = {12'b0, i_apb_subsystem.i_ahb2apb.psel8, i_apb_subsystem.i_ahb2apb.psel2, i_apb_subsystem.i_ahb2apb.psel1, i_apb_subsystem.i_ahb2apb.psel0};
  assign apbi_mo.prdata = i_apb_subsystem.i_ahb2apb.psel0? i_apb_subsystem.i_ahb2apb.prdata0 : (i_apb_subsystem.i_ahb2apb.psel1? i_apb_subsystem.i_ahb2apb.prdata1 : (i_apb_subsystem.i_ahb2apb.psel2? i_apb_subsystem.i_ahb2apb.prdata2 : i_apb_subsystem.i_ahb2apb.prdata8));

  assign spi_s0.sig_n_ss_in = n_ss_out[0];
  assign spi_s0.sig_n_p_reset = hresetn;
  assign spi_s0.sig_pclk = tb_hclk;

  assign gpio_s0.n_p_reset = hresetn;
  assign gpio_s0.pclk = tb_hclk;

  assign hwdata_byte_alligned = (ahbi_m0.AHB_HADDR[1:0] == 2'b00) ? ahbi_m0.AHB_HWDATA : {4{ahbi_m0.AHB_HWDATA[7:0]}};

  apb_subsystem_0 i_apb_subsystem (
    // Inputs
    // system signals
    .hclk              (tb_hclk),     // AHB Clock
    .n_hreset          (hresetn),     // AHB reset - Active low
    .pclk              (tb_hclk),     // APB Clock
    .n_preset          (hresetn),     // APB reset - Active low
    
    // AHB interface for AHB2APM bridge
    .hsel     (1'b1),        // AHB2APB select
    .haddr             (ahbi_m0.AHB_HADDR),        // Address bus
    .htrans            (ahbi_m0.AHB_HTRANS),       // Transfer type
    .hsize             (ahbi_m0.AHB_HSIZE),        // AHB Access type - byte half-word word
    .hwrite            (ahbi_m0.AHB_HWRITE),       // Write signal
    .hwdata            (hwdata_byte_alligned),       // Write data
    .hready_in         (hready),       // Indicates that the last master has finished 
                                       // its bus access
    .hburst            (ahbi_m0.AHB_HBURST),       // Burst type
    .hprot             (ahbi_m0.AHB_HPROT),        // Protection control
    .hmaster           (4'h0),      // Master select
    .hmastlock         (ahbi_m0.AHB_HLOCK),  // Locked transfer
    // AHB interface for SMC
    .smc_hclk          (1'b0),
    .smc_n_hclk        (1'b1),
    .smc_haddr         (32'd0),
    .smc_htrans        (2'b00),
    .smc_hsel          (1'b0),
    .smc_hwrite        (1'b0),
    .smc_hsize         (3'd0),
    .smc_hwdata        (32'd0),
    .smc_hready_in     (1'b1),
    .smc_hburst        (3'b000),
    .smc_hprot         (4'b0000),
    .smc_hmaster       (4'b0000),
    .smc_hmastlock     (1'b0),

    //interrupt from DMA
    .DMA_irq           (1'b0),      

    // Scan inputs
    .scan_en           (1'b0),         // Scan enable pin
    .scan_in_1         (1'b0),         // Scan input for first chain
    .scan_in_2         (1'b0),        // Scan input for second chain
    .scan_mode         (1'b0),
    //input for smc
    .data_smc          (32'd0),
    //inputs for uart
    .ua_rxd            (uart_s0.txd),
    .ua_rxd1           (uart_s1.txd),
    .ua_ncts           (uart_s0.cts_n),
    .ua_ncts1          (uart_s1.cts_n),
    //inputs for spi
    .n_ss_in           (1'b1),
    .mi                (spi_s0.sig_so),
    .si                (1'b0),
    .sclk_in           (1'b0),
    //inputs for GPIO
    .gpio_pin_in       (gpio_s0.gpio_pin_in[15:0]),
 
//interrupt from Enet MAC
     .macb0_int     (1'b0),
     .macb1_int     (1'b0),
     .macb2_int     (1'b0),
     .macb3_int     (1'b0),

    // Scan outputs
    .scan_out_1        (),             // Scan out for chain 1
    .scan_out_2        (),             // Scan out for chain 2
   
    //output from APB 
    // AHB interface for AHB2APB bridge
    .hrdata            (hrdata),       // Read data provided from target slave
    .hready            (hready),       // Ready for new bus cycle from target slave
    .hresp             (hresp),        // Response from the bridge

    // AHB interface for SMC
    .smc_hrdata        (), 
    .smc_hready        (),
    .smc_hresp         (),
  
    //outputs from smc
    .smc_n_ext_oe      (),
    .smc_data          (),
    .smc_addr          (),
    .smc_n_be          (),
    .smc_n_cs          (), 
    .smc_n_we          (),
    .smc_n_wr          (),
    .smc_n_rd          (),
    //outputs from uart
    .ua_txd             (uart_s0.rxd),
    .ua_txd1            (uart_s1.rxd),
    .ua_nrts            (uart_s0.rts_n),
    .ua_nrts1           (uart_s1.rts_n),
    // outputs from ttc
    .so                (),
    .mo                (spi_s0.sig_si),
    .sclk_out          (spi_s0.sig_sclk_in),
    .n_ss_out          (n_ss_out[7:0]),
    .n_so_en           (),
    .n_mo_en           (),
    .n_sclk_en         (),
    .n_ss_en           (),
    //outputs from gpio
    .n_gpio_pin_oe     (gpio_s0.n_gpio_pin_oe[15:0]),
    .gpio_pin_out      (gpio_s0.gpio_pin_out[15:0]),

//unconnected o/p ports
    .clk_SRPG_macb0_en(),
    .clk_SRPG_macb1_en(),
    .clk_SRPG_macb2_en(),
    .clk_SRPG_macb3_en(),
    .core06v(),
    .core08v(),
    .core10v(),
    .core12v(),
    .mte_smc_start(),
    .mte_uart_start(),
    .mte_smc_uart_start(),
    .mte_pm_smc_to_default_start(),
    .mte_pm_uart_to_default_start(),
    .mte_pm_smc_uart_to_default_start(),
    .pcm_irq(),
    .ttc_irq(),
    .gpio_irq(),
    .uart0_irq(),
    .uart1_irq(),
    .spi_irq(),

    .macb3_wakeup(),
    .macb2_wakeup(),
    .macb1_wakeup(),
    .macb0_wakeup()
);


initial
begin
  tb_hclk = 0;
  hresetn = 1;

  #1 hresetn = 0;
  #1200 hresetn = 1;
end

always #50 tb_hclk = ~tb_hclk;

initial begin
  uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.ve.uart0*", "vif", uart_s0);
  uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.ve.uart1*", "vif", uart_s1);
  uvm_config_db#(virtual uart_ctrl_internal_if)::set(null, "uvm_test_top.ve.apb_ss_env.apb_uart0.*", "vif", uart_int0);
  uvm_config_db#(virtual uart_ctrl_internal_if)::set(null, "uvm_test_top.ve.apb_ss_env.apb_uart1.*", "vif", uart_int1);
  uvm_config_db#(virtual apb_if)::set(null, "uvm_test_top.ve.apb0*", "vif", apbi_mo);
  uvm_config_db#(virtual ahb_if)::set(null, "uvm_test_top.ve.ahb0*", "vif", ahbi_m0);
  uvm_config_db#(virtual spi_if)::set(null, "uvm_test_top.ve.spi0*", "spi_if", spi_s0);
  uvm_config_db#(virtual gpio_if)::set(null, "uvm_test_top.ve.gpio0*", "gpio_if", gpio_s0);
  run_test();
end

endmodule
