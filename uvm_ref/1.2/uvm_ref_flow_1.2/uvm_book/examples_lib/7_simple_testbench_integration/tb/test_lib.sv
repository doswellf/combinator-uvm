/*-------------------------------------------------------------------------
File name   : test_lib.sv
Title       : Library of tests
Project     :
Created     :
Description : Library of tests for the UART CONTROLLER Environment
Notes       : Includes all the base test and all test files.
----------------------------------------------------------------------*/

class uart_ctrl_base_test extends uvm_test;
uart_ctrl_tb uart_ctrl_tb0;

`uvm_component_utils(uart_ctrl_base_test)

virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0", this);
endfunction : build_phase

task run_phase(uvm_phase phase);
  super.run_phase(phase);
  this.print();
endtask : run_phase

function new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

endclass : uart_ctrl_base_test

class u2a_a2u_rand_test extends uart_ctrl_base_test;
  
`uvm_component_utils(u2a_a2u_rand_test)

virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  set_config_string("uart_ctrl_tb0.apb0.master.sequencer", "default_sequence", "apb_write_to_uart_seq");
  set_config_string("uart_ctrl_tb0.uart0.Tx.sequencer", "default_sequence", "uart_write_to_apb_seq");
endfunction : build_phase

function new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

endclass : u2a_a2u_rand_test

class apb_write_to_uart_seq extends uvm_sequence #(apb_transfer);

`uvm_object_utils(apb_write_to_uart_seq)
`uvm_declare_p_sequencer(apb_master_sequencer)

function new(string name="apb_write_to_uart_seq");
  super.new(name);
endfunction : new

task body();
  `uvm_info(get_type_name(), "Executing...", UVM_LOW)
  // Actual details of the sequence go here...
endtask : body


endclass : apb_write_to_uart_seq

class uart_write_to_apb_seq extends uvm_sequence #(uart_frame);

`uvm_object_utils(uart_write_to_apb_seq)
`uvm_declare_p_sequencer(uart_sequencer)

function new(string name="uart_write_to_apb_seq");
  super.new(name);
endfunction : new

task body();
  `uvm_info(get_type_name(), "Executing...", UVM_LOW)
  // Actual details of the sequence go here...
endtask : body

endclass : uart_write_to_apb_seq
