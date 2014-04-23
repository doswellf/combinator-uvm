/****************************************************************
  Example 7-9: UART Frame Data Item

  To run:   %  irun -uvm ex7-9_uart_frame.sv -svseed random

  OR:       %  irun -uvmhome $UVM_HOME ex7-9_uart_frame.sv
****************************************************************/

module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
/*------------------------------------------------------------------
 Original File: ../interface_uvc_lib/uart/sv/uart_frame.sv
--------------------------------------------------------------------*/
// Parity Type Control knob
typedef enum bit {GOOD_PARITY, BAD_PARITY} parity_e;

class uart_frame extends uvm_sequence_item; 
  // UART Frame
  rand bit start_bit;
  rand bit [7:0] payload;
  rand bit [1:0] stop_bits;
  rand bit [3:0] error_bits;
  bit parity;
 
  // Control Fields
  rand int transmit_delay;
  rand parity_e parity_type;

  // Default constraints
  constraint default_error_bits { error_bits != 4'b0000;}
  constraint default_parity_type { parity_type dist {GOOD_PARITY:=90, BAD_PARITY:=10};}
  constraint default_txmit_delay {transmit_delay >= 0; transmit_delay < 20;}
  constraint default_start_bit { start_bit == 1'b0;}
  constraint default_stop_bits { stop_bits == 2'b11;}

  // These declarations implement the create() and get_type_name() 
  // and enable automation of the uart_frame's fields   
  `uvm_object_utils_begin(uart_frame)   
    `uvm_field_int(start_bit, UVM_DEFAULT)
    `uvm_field_int(payload, UVM_DEFAULT)  
    `uvm_field_int(parity, UVM_DEFAULT)  
    `uvm_field_int(stop_bits, UVM_DEFAULT)
    `uvm_field_int(error_bits, UVM_DEFAULT)
    `uvm_field_enum(parity_e,parity_type, UVM_DEFAULT + UVM_NOCOMPARE) 
    `uvm_field_int(transmit_delay, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE + UVM_NOCOPY)
  `uvm_object_utils_end

  // Constructor - required UVM syntax
  function new(string name = "uart_frame");
    super.new(name);
  endfunction 
   
  // This method calculates the parity
  function bit calc_parity(int unsigned num_of_data_bits=8,
                           bit[1:0] ParityMode=0);
    bit temp_parity;

    if (num_of_data_bits == 6)
      temp_parity = ^payload[5:0];  
    else if (num_of_data_bits == 7)
      temp_parity = ^payload[6:0];  
    else
      temp_parity = ^payload;  

    case(ParityMode[0])
      0: temp_parity = ~temp_parity;
      1: temp_parity = temp_parity;
    endcase
    case(ParityMode[1])
      0: temp_parity = temp_parity;
      1: temp_parity = ~ParityMode[0];
    endcase
    if (parity_type == BAD_PARITY)
      calc_parity = ~temp_parity;
    else 
      calc_parity = temp_parity;
  endfunction 

  // Parity is calculated in the post_randomize() method
  function void post_randomize();
    if (parity_type == BAD_PARITY)
      parity = ~calc_parity();
    else parity = calc_parity();
  endfunction : post_randomize

endclass : uart_frame


uart_frame frame;

initial begin
   frame = new("frame");
   repeat (3) begin
     void'(frame.randomize());
     frame.print();
   end
end

endmodule : test
