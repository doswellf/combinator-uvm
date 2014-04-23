/*-------------------------------------------------------------------------
File name   : ex7-8_uart_ctrl_test.sv
Description : 
Notes       : This file is not executable as a standalone test.
----------------------------------------------------------------------*/

class u2a_a2u_rand_test extends uart_ctrl_base_test;
  
`uvm_component_utils(u2a_a2u_rand_test)

virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  uvm_config_wrapper::set(this, "uart_ctrl_tb0.apb0.master.sequencer.run_phase",
           "default_sequence", apb_write_to_uart_seq::type_id::get());
  uvm_config_wrapper::set(this, "uart_ctrl_tb0.uart0.Tx.sequencer.run_phase",
           "default_sequence", uart_write_to_apb_seq::type_id::get());
endfunction : build_phase

function new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

endclass : u2a_a2u_rand_test
