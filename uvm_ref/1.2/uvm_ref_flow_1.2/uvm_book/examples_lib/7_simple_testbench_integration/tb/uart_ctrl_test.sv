/****************************************************************
  Example : UART Controller Test

  To run:   %  irun -f run.f 
****************************************************************/

module top;
  //UVM Library
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Interface UVC Components
  import apb_pkg::*;   // APB UVC
  import uart_pkg::*;  // UART UVC

  // Include UART CONTROLLER Files
  `include "sv/uart_ctrl_defines.svh"
  `include "sv/uart_ctrl_config.sv"
  `include "sv/uart_ctrl_virtual_sequencer.sv"
  `include "sv/uart_ctrl_scoreboard.sv"
  
  // UART CONTROLLER Simple Testbench FILE
  `include "tb/uart_ctrl_simple_tb.sv"
  `include "tb/test_lib1.sv"

bit clk, reset;

apb_if  apb_if0(clk, reset);
uart_if uart_if0(clk, reset);

initial begin
  reset <= 1'b0;
  clk <= 1'b0;
  #51 reset <= 1'b1;
end
always #5 clk = ~clk;

initial begin
  // Configure the virtual interfaces
  uvm_config_db#(virtual apb_if)::set(null, "uvm_test_top.uart_ctrl_tb0.apb0*", "vif", apb_if0);
  uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.uart_ctrl_tb0.uart0*", "vif", uart_if0);

  run_test();
end

endmodule : top
