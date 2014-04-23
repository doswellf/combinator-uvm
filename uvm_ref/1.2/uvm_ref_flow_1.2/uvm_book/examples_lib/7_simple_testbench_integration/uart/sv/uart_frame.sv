/*-------------------------------------------------------------------------
File name   : uart_frame.sv
Title       : TX frame file for uart uvc
Project     :
Created     :
Description : Describes UART Transmit Frame data structure
Notes       :  
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------


`ifndef UART_FRAME_SVH
`define UART_FRAME_SVH

// Parity Type Control knob
typedef enum bit {GOOD_PARITY, BAD_PARITY} parity_e;

class uart_frame extends uvm_sequence_item;  //lab1_note1
  // UART Frame
  rand bit start_bit;
  rand bit [7:0] payload;
  bit parity;
  rand bit [1:0] stop_bits;
  rand bit [3:0] error_bits;
 
  // Control Knobs
  rand parity_e parity_type;
  rand int transmit_delay;

  // Default constraints  //lab1_note2
  constraint default_txmit_delay {transmit_delay >= 0; transmit_delay < 20;}
  constraint default_start_bit { start_bit == 1'b0;}
  constraint default_stop_bits { stop_bits == 2'b11;}
  constraint default_parity_type { parity_type==GOOD_PARITY;}
  constraint default_error_bits { error_bits == 4'b0000;}

  // These declarations implement the create() and get_type_name() 
  // and enable automation of the uart_frame's fields     //lab1_note3
  `uvm_object_utils_begin(uart_frame)   
    `uvm_field_int(start_bit, UVM_DEFAULT)
    `uvm_field_int(payload, UVM_DEFAULT)  
    `uvm_field_int(parity, UVM_DEFAULT)  
    `uvm_field_int(stop_bits, UVM_DEFAULT)
    `uvm_field_int(error_bits, UVM_DEFAULT)
    `uvm_field_enum(parity_e,parity_type, UVM_DEFAULT + UVM_NOCOMPARE) 
    `uvm_field_int(transmit_delay, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE + UVM_NOCOPY)
  `uvm_object_utils_end

  // Constructor - required UVM syntax  //lab1_note4
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

  // Parity is calculated in the post_randomize() method   //lab1_note5
  function void post_randomize();
   parity = calc_parity();
  endfunction : post_randomize

endclass

`endif
