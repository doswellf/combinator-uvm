/*-------------------------------------------------------------------------
File name   : uart_data_auto_lab1.sv
Title       : Test Case
Project     :
Created     :
Description : One test case for WorkShop lab1 - URM Data Automation
Notes       : The test creates a uart_ctrl_tb and sets the default
            : sequence for the sequencer as concurrent_u2a_a2u_rand_trans
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

class uart_uvm_lab1 extends uart_pkg::uart_frame;

  `uvm_object_utils_begin(uart_uvm_lab1)  
    `uvm_field_int(start_bit, UVM_ALL_ON)
    `uvm_field_int(payload, UVM_ALL_ON)
    `uvm_field_int(stop_bits, UVM_ALL_ON)
    `uvm_field_int(error_bits, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "");
	  super.new(name);
  endfunction 

endclass : uart_uvm_lab1

class uart_data_automation_lab1 extends apb_uart_rx_tx;

  `uvm_component_utils(uart_data_automation_lab1)

  function new(input string name, input uvm_component parent);
      super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    set_type_override_by_type(uart_pkg::uart_frame::get_type(), uart_uvm_lab1::get_type());
    super.build_phase(phase);
  endfunction : build_phase

endclass
