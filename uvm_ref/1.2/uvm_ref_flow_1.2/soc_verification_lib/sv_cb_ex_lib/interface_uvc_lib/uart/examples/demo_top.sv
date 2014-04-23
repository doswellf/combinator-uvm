/*-----------------------------------------------------------------
File name     : demo_top.sv
Developers    : Kathleen Meade
Created       : Tue May  4 15:13:46 2010
Description   :
Notes         :
-------------------------------------------------------------------
Copyright 2010 (c) Cadence Design Systems
-----------------------------------------------------------------*/

`include "dut_dummy.v"
`include "uart_if.sv"
`include "uart_pkg.sv"

module demo_top;

  // Import the UVM Package
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Import the UART UVC Package
  import uart_pkg::*;

  // Import the test library
  `include "test_lib.sv"

  reg clock;
  reg reset;

  uart_if uart_if_0(clock, reset);
  
  dut_dummy dut( .clock(clock),
                 .reset(reset),
                 .uart_if0(uart_if_0)
               );

  initial begin
    uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.demo_tb0.uart0*", "vif", uart_if_0);
    run_test();
  end

  initial begin
    reset <= 1'b0;
    clock <= 1'b1;
    #51 reset = 1'b1;
  end

  //Generate Clock
  always #5 clock = ~clock;

endmodule
