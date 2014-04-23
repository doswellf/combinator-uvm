/*-------------------------------------------------------------------------
File name   : uart_ctrl_top.sv
Title       : Top level file
Description : This file implements the top level test bench for the 
            : UART Controller environment
Notes       : The uart_ctrl_top module instantiates the UART DUT, 
            : APB master interface, UART interface and connects 
            : them appropriatly
----------------------------------------------------------------------*/
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

// Interfaces
`include "apb_if.sv"
`include "apb_master_if.sv"
`include "apb_slave_if.sv"
`include "uart_if.sv"
`include "coverage/uart_ctrl_internal_if.sv"

module uart_ctrl_top;
  // Import the UVM Library and UVM macros
  import uvm_pkg::*;             //UVM Library Package
  `include "uvm_macros.svh"

  // Other packages
  import uart_pkg::*;       //UART UVC Package
  import apb_pkg::*;        //APB UVC Package
  import uart_ctrl_pkg::*;  //UART MODULE UVC Package

  // UART Controller testbench
  `include "uart_ctrl_tb.sv"

  // UART Controller tests (in ../tests directory)
  `include "test_lib.sv"
 
  reg clock;
  reg reset;

  wire [3:0] wb_sel;
  wire [31:0] dummy_dbus;
  wire [31:0] dummy_rdbus;
  reg [2:0] div8_clk;

  apb_if                apb_if0(.pclock(clock), .preset(reset));
  apb_master_if         apb_mi0(.pclock(clock), .preset(reset));
  apb_slave_if          apb_si0(.pclock(clock), .preset(reset));
  uart_if               uart_if0(.clock(div8_clk[2]), .reset(reset));
  uart_ctrl_internal_if uart_int0(.clock(div8_clk[2]));

  assign wb_sel = (apb_if0.paddr[1:0] == 0) ? 4'b0001 : (apb_if0.paddr[1:0] == 1 ? 4'b0010 : (apb_if0.paddr[1:0] == 2 ? 4'b0100 : 4'b1000)); 
  assign dummy_dbus = {4{apb_if0.pwdata[7:0]}};
  assign apb_if0.prdata[7:0] = dummy_rdbus[31:24] | dummy_rdbus[23:16] | dummy_rdbus[15:8] | dummy_rdbus[7:0];

  assign uart_int0.tx_fifo_ptr = uart_dut.regs.transmitter.tf_count;
  assign uart_int0.rx_fifo_ptr = uart_dut.regs.receiver.rf_count;

 always @(posedge clock) begin
   if (!reset)
     div8_clk = 3'b000;
   else
     div8_clk = div8_clk + 1;
 end

  //RTL Instantiation
  uart_top uart_dut(
	.wb_clk_i(clock), 
	
	// Wishbone signals
	.wb_rst_i(~reset),
        .wb_adr_i(apb_if0.paddr[4:0]),
        .wb_dat_i(dummy_dbus),
        .wb_dat_o(dummy_rdbus),
        .wb_we_i(apb_if0.prwd),
        .wb_stb_i(apb_if0.psel[0]),
        .wb_cyc_i(apb_if0.psel[0]),
        .wb_ack_o(apb_if0.pready),
        .wb_sel_i(wb_sel),
	.int_o(), // interrupt request

	// UART	signals
	// serial input/output
	.stx_pad_o(uart_if0.rxd),
        .srx_pad_i(uart_if0.txd),

	// modem signals
	.rts_pad_o(rts_n),
        .cts_pad_i(uart_if0.cts_n),
        .dtr_pad_o(uart_if0.dtr_n),
        .dsr_pad_i(uart_if0.dsr_n),
        .ri_pad_i(uart_if0.ri_n),
        .dcd_pad_i(uart_if0.dcd_n)
  );

  function bit _init_vif_function();
  // Configure Virtual Interfaces
  uvm_config_db#(virtual uart_ctrl_internal_if)::set(null, "uvm_test_top.uart_ctrl_tb0.uart_ctrl0.*", "vif", uart_int0);
  uvm_config_db#(virtual apb_if)::set(null, "uvm_test_top.uart_ctrl_tb0.apb0*", "vif", apb_if0);
  uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.uart_ctrl_tb0.uart0*", "vif", uart_if0);
  endfunction

  bit init_vif = _init_vif_function();

  initial begin
   // Run the UVM Test
    run_test();
  end

  initial begin
    reset <= 1'b0;
    clock <= 1'b0;
    #51 reset <= 1'b1;
  end

  //Generate Clock
  always
    #5 clock = ~clock;

  final begin
    $display("=======================================================");
    $display("UART CONTROLLER DUT REGISTERS:");
    $displayh("uart_ctrl_top.uart_dut.regs.dl  =", uart_ctrl_top.uart_dut.regs.dl);
    $displayh("uart_ctrl_top.uart_dut.regs.fcr = ", uart_ctrl_top.uart_dut.regs.fcr);
    $displayh("uart_ctrl_top.uart_dut.regs.ier = ", uart_ctrl_top.uart_dut.regs.ier);
    $displayh("uart_ctrl_top.uart_dut.regs.iir = ", uart_ctrl_top.uart_dut.regs.iir);
    $displayh("uart_ctrl_top.uart_dut.regs.lcr = ", uart_ctrl_top.uart_dut.regs.lcr);
    $display("=======================================================");
  end

endmodule : uart_ctrl_top
