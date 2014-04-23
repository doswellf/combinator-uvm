/*-------------------------------------------------------------------------
File name   : ex7-10_uart_ctrl_override_test.sv
Description : 
Notes       : This file is not executable as a standalone test.
----------------------------------------------------------------------*/

class short_delay_frame extends uart_frame;
  // This constraint further limits the delay values.
  constraint c_test1_txmit_delay {transmit_delay  < 10;}
 `uvm_object_utils(short_delay_frame)
  function new(string name="short_delay_frame");
    super.new(name);
  endfunction : new
endclass: short_delay_frame

// TEST from EXample 7-10
class short_delay_test extends uart_ctrl_base_test;
  
`uvm_component_utils(short_delay_test)
function new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Use short_delay_frame throughout the environment
  factory.set_type_override_by_type(uart_frame::get_type(),
     short_delay_frame::get_type());
  uvm_config_wrapper::set(this, "uart_ctrl_tb0.apb0.master.sequencer.run_phase",
           "default_sequence", apb_write_to_uart_seq::type_id::get());
  uvm_config_wrapper::set(this, "uart_ctrl_tb0.uart0.Tx.sequencer.run_phase",
           "default_sequence", uart_write_to_apb_seq::type_id::get());
endfunction : build_phase

endclass : short_delay_test
