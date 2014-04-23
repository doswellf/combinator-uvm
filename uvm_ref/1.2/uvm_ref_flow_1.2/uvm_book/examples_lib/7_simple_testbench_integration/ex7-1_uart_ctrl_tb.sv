/****************************************************************
  Example 7-1: UART Controller Testbench 

  To run:   %  irun -f run.f ex7-1_uart_ctrl_tb.sv
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

class uart_ctrl_tb extends uvm_env;

  // Interface UVC Components
  apb_pkg::apb_env apb0;     // APB UVC
  uart_pkg::uart_env uart0;  // UART UVC

  // Scoreboard
  uart_ctrl_tx_scbd tx_scbd;
  uart_ctrl_rx_scbd rx_scbd;

  // Virtual Sequencer
  uart_ctrl_virtual_sequencer virtual_sequencer;

  // UVC Configuration Classes
  apb_config apb_cfg;
  uart_config uart_cfg;

  // UVM Component Automation
  `uvm_component_utils(uart_ctrl_tb)

  // Constructor - required UVM syntax
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Additional Class Methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
endclass : uart_ctrl_tb

function void uart_ctrl_tb::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Create UVC configuration if it has not already been set
  if (apb_cfg == null) begin
    apb_cfg = apb_config::type_id::create("apb_cfg", this);
    apb_cfg.add_master("master", UVM_ACTIVE);
    apb_cfg.add_slave("slave0", 32'h00000000, 32'h81FFFFFF, 0, UVM_PASSIVE);
  end
  if (uart_cfg == null) begin
    uart_cfg = uart_config::type_id::create("uart_cfg", this);
  end
  uvm_config_db#(apb_config)::set(this, "apb0*", "cfg", apb_cfg);
  uvm_config_db#(uart_config)::set(this, "uart0*", "cfg", uart_cfg);
  uvm_config_db#(uart_config)::set(this, "*scbd*", "uart_cfg", uart_cfg);
  uvm_config_db#(apb_slave_config)::set(this, "*scbd*", "slave_cfg", apb_cfg.slave_configs[0]);

  // Create sub-components
  apb0 = apb_env::type_id::create("apb0", this);
  uart0 = uart_env::type_id::create("uart0", this);
  virtual_sequencer = uart_ctrl_virtual_sequencer::type_id::create("virtual_sequencer", this);
  tx_scbd = uart_ctrl_tx_scbd::type_id::create("tx_scbd", this);
  rx_scbd = uart_ctrl_rx_scbd::type_id::create("rx_scbd", this);
endfunction : build_phase

function void uart_ctrl_tb::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // Connect TLM ports from monitors to scoreboards
  uart0.Rx.monitor.frame_collected_port.connect(rx_scbd.uart_match);
  apb0.bus_monitor.item_collected_port.connect(rx_scbd.apb_add);
  uart0.Tx.monitor.frame_collected_port.connect(tx_scbd.uart_add);
  apb0.bus_monitor.item_collected_port.connect(tx_scbd.apb_match);

  // Hook up virtual sequencer to interface sequencers
  virtual_sequencer.apb_seqr =  apb0.master.sequencer;
  if (uart0.Tx.get_is_active() == UVM_ACTIVE)
     virtual_sequencer.uart_seqr =  uart0.Tx.sequencer;

endfunction : connect_phase

// Simple Test Class to create TB and print hierarchy
  `include "tb/simple_test.sv"

bit clk, reset;

apb_if apb_if0(clk, reset);
uart_if uart_if0(clk, reset);

initial begin
// Set the Virtual Interfaces for this Design
 uvm_config_db#(virtual apb_if)::set(null, "*.my_tb.apb0*", "vif", apb_if0);
 uvm_config_db#(virtual uart_if)::set(null, "*.my_tb.uart0*", "vif", uart_if0);
// Run a SIMPLE test so Hierarchy can be printed.
 run_test("simple_test");
end

endmodule : test
