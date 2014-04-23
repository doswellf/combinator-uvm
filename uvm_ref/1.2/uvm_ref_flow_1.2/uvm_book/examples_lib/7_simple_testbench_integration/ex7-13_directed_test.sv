/****************************************************************
  Example 7-13 : Directed Test

  To run:   %  irun -f run.f ex7-13_directed_test.sv
****************************************************************/

module test;
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

  `include "tb/test_lib.sv"

//  Directed Test Class Definition
class config_uart_ctrl_test extends uart_ctrl_base_test;

  `uvm_component_utils(config_uart_ctrl_test)

  //uart_ctrl_tb uart_ctrl_tb0;   // Testbench
  
  function new(string name="config_uart_ctrl_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create the testbench
   // uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0", this);
  endfunction : build_phase

  // run_phase() Executes the test
  virtual task run_phase(uvm_phase phase);
    apb_transfer transfer;
    super.run_phase(phase);
    phase.raise_objection(this, "Test: config_uart_ctrl_test");
    transfer = apb_transfer::type_id::create("transfer", this);
    #100 // Wait for reset to be finished
    $finish; // TEMPORARY FINISH
    // Set the Line Control Reg to 8'h83
    transfer.addr = 8'h03;
    transfer.data = 8'h83;
    transfer.direction = APB_WRITE;
    transfer.transmit_delay = 1;
    uart_ctrl_tb0.apb0.master.sequencer.execute_item(transfer);
    // Set the Div Latch 1 to 8'h01
    transfer.addr = 8'h00;
    transfer.data = 8'h01;
    uart_ctrl_tb0.apb0.master.sequencer.execute_item(transfer);
    // Set the Div Latch 2 to 8'h00
    transfer.addr = 8'h01;
    transfer.data = 8'h00;
    uart_ctrl_tb0.apb0.master.sequencer.execute_item(transfer);
    // Set the Line Control Reg to 8'h03
    transfer.addr = 8'h03;
    transfer.data = 8'h03;
    uart_ctrl_tb0.apb0.master.sequencer.execute_item(transfer);
    #300 // wait for seqencer/driver to finish executing transfer
    phase.drop_objection(this, "Test: config_uart_ctrl_test");
  endtask : run_phase
endclass : config_uart_ctrl_test

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

  run_test("config_uart_ctrl_test");
end

endmodule : test
