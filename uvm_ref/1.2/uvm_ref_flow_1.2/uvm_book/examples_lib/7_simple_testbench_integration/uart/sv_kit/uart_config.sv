/*-------------------------------------------------------------------------
File name   : uart_config.sv
Title       : configuration file
Project     :
Created     :
Description : This file contains configuration information for the UART
              device
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


`ifndef UART_CONFIG_SV
`define UART_CONFIG_SV

class uart_config extends uvm_object;
  //UART topology parameters
  uvm_active_passive_enum  is_tx_active = UVM_ACTIVE;
  uvm_active_passive_enum  is_rx_active = UVM_PASSIVE;

  // UART device parameters
  rand bit [7:0]    baud_rate_gen;  // Baud Rate Generator Register
  rand bit [7:0]    baud_rate_div;  // Baud Rate Divider Register

  // Line Control Register Fields
  rand bit [1:0]    char_length; // Character length (ua_lcr[1:0])
  rand bit          nbstop;        // Number stop bits (ua_lcr[2])
  rand bit          parity_en ;    // Parity Enable    (ua_lcr[3])
  rand bit [1:0]    parity_mode;   // Parity Mode      (ua_lcr[5:4])

  int unsigned chrl;  
  int unsigned stop_bt;  

  // Control Register Fields
  rand bit          cts_en ;
  rand bit          rts_en ;

 // Calculated in post_randomize() so not randomized
  byte unsigned char_len_val;      // (8, 7 or 6)
  byte unsigned stop_bit_val;      // (1, 1.5 or 2)

  // These default constraints can be overriden
  // Constrain configuration based on UVC/RTL capabilities
//  constraint c_num_stop_bits  { nbstop      inside {[0:1]};}
  constraint c_bgen          { baud_rate_gen       == 1;}
  constraint c_brgr          { baud_rate_div       == 0;}
  constraint c_rts_en         { rts_en      == 0;}
  constraint c_cts_en         { cts_en      == 0;}

  // These declarations implement the create() and get_type_name()
  // as well as enable automation of the tx_frame's fields   
  `uvm_object_utils_begin(uart_config)
    `uvm_field_enum(uvm_active_passive_enum, is_tx_active, UVM_DEFAULT)
    `uvm_field_enum(uvm_active_passive_enum, is_rx_active, UVM_DEFAULT)
    `uvm_field_int(baud_rate_gen, UVM_DEFAULT + UVM_DEC)
    `uvm_field_int(baud_rate_div, UVM_DEFAULT + UVM_DEC)
    `uvm_field_int(char_length, UVM_DEFAULT)
    `uvm_field_int(nbstop, UVM_DEFAULT )  
    `uvm_field_int(parity_en, UVM_DEFAULT)
    `uvm_field_int(parity_mode, UVM_DEFAULT)
  `uvm_object_utils_end
     
  // This requires for registration of the ptp_tx_frame   
  function new(string name = "uart_config");
    super.new(name);
  endfunction 
   
  function void post_randomize();
    ConvToIntChrl();
    ConvToIntStpBt();
  endfunction 

  // Function to convert the 2 bit Character length to integer
  function void ConvToIntChrl();
    case(char_length)
      2'b00 : char_len_val = 5;
      2'b01 : char_len_val = 6;
      2'b10 : char_len_val = 7;
      2'b11 : char_len_val = 8;
      default : char_len_val = 8;
    endcase
  endfunction : ConvToIntChrl
    
  // Function to convert the 2 bit stop bit to integer
  function void ConvToIntStpBt();
    case(nbstop)
      2'b00 : stop_bit_val = 1;
      2'b01 : stop_bit_val = 2;
      default : stop_bit_val = 2;
    endcase
  endfunction : ConvToIntStpBt
    
endclass
`endif  // UART_CONFIG_SV
