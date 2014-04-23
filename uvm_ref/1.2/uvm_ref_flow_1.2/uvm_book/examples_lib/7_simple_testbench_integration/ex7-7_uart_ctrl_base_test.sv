/*-------------------------------------------------------------------------
File name   : ex7-7_uart_ctrl_base_test.sv
Description : 
Notes       : This file is not executable as a standalone test.
----------------------------------------------------------------------*/

class uart_ctrl_base_test extends uvm_test;

 uart_ctrl_tb uart_ctrl_tb0;

 `uvm_component_utils(uart_ctrl_base_test)

 function new(input string name, input uvm_component parent = null);
   super.new(name, parent);
 endfunction  

 virtual function void build_phase(uvm_phase phase);
   super.build_phase(phase);
   uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0", this);
 endfunction 

 virtual task run_phase(uvm_phase phase);
   uart_ctrl_tb0.print();
 endtask

endclass : uart_ctrl_base_test
