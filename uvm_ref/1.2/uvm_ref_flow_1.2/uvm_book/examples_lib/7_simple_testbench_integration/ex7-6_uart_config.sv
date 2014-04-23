/****************************************************************
  Example 7-6: UART Configuration Classe

  To run:   %  irun -uvm ex7-6_uart_config.sv
****************************************************************/
module test;
  //UVM Library
  import uvm_pkg::*;
  `include "uvm_macros.svh"

/***************************************************************************
  FILE: ../interface_uvc_lib/uart/sv/uart_config.sv
  This file contains configuration information for the UART device
***************************************************************************/

class uart_config extends uvm_object;
  //UART topology parameters
  uvm_active_passive_enum  is_tx_active = UVM_ACTIVE;
  uvm_active_passive_enum  is_rx_active = UVM_PASSIVE;

  // UART device parameters
  //rand bit [7:0]    baud_rate_gen=1;  // Baud Rate Generator Register
  rand bit [7:0]    baud_rate_gen;  // Baud Rate Generator Register
  rand bit [7:0]    baud_rate_div;  // Baud Rate Divider Register

  // Line Control Register Fields
  rand bit [1:0]    char_length = 2; // Character length (ua_lcr[1:0])
  rand bit          nbstop=1;        // Number stop bits (ua_lcr[2])
  rand bit          parity_en ;    // Parity Enable    (ua_lcr[3])
  rand bit          parity_even;   // Parity Even      (ua_lcr[4])
  rand bit          parity_stick;  // Parity Stick     (ua_lcr[5])
  rand bit [1:0]    parity_mode=1;   // Parity Mode      (ua_lcr[5:4])
  rand bit          break_ctl;     // Break Control    (ua_lcr[6])
  rand bit          dl_access;     // Divisor Latch    (ua_lcr[7])

  rand bit [1:0]    ua_chmode;     // Channel mode     (ua_lcr[9:8])
                                   // 00 = Normal, 01 = Auto echo,
                                   // 10 = Local Loopback, 11 = Remote loopback
  // Control Register Fields
  rand bit          rx_en = 1'b1;  // RX Enable (ua_cr[2])
  rand bit          tx_en = 1'b1;  // TX Enable (ua_cr[4])
  rand bit          cts_en ;
  rand bit          rts_en ;

  rand bit [10:0]   ua_ier;        // Interrupt Enable Register    
  rand bit [10:0]   ua_idr;        // Interrupt Disable Register    
  rand bit [4:0]    ua_rtrig;      // Receiver Fifo Trigger level
  
 // Calculated in post_randomize() so not randomized
  byte unsigned char_len_val;      // (8, 7 or 6)
  byte unsigned stop_bit_val;      // (1, 1.5 or 2)

  // These default constraints can be overriden
  // Constrain configuration based on UVC/RTL capabilities
  constraint c_num_stop_bits  { nbstop      inside {[0:2]};}
  constraint c_parity_mode    { parity_mode == {parity_stick, parity_even};}
  constraint c_tx_en          { tx_en       == 1;}
  constraint c_rx_en          { rx_en       == 1;}
  constraint c_rts_en         { rts_en      == 0;}
  constraint c_cts_en         { cts_en      == 0;}
  constraint c_ua_chmode      { ua_chmode   == 2'b00;}

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
    //`uvm_field_int(parity_even, UVM_DEFAULT)
    //`uvm_field_int(parity_stick, UVM_DEFAULT)
    `uvm_field_int(parity_mode, UVM_DEFAULT)
    //`uvm_field_int(break_ctl, UVM_DEFAULT)
    //`uvm_field_int(dl_access, UVM_DEFAULT)
    `uvm_field_int(ua_chmode, UVM_DEFAULT)
    //`uvm_field_int(rx_en, UVM_DEFAULT)
    //`uvm_field_int(tx_en, UVM_DEFAULT)
    //`uvm_field_int(cts_en, UVM_DEFAULT)
    //`uvm_field_int(rts_en, UVM_DEFAULT)
    //`uvm_field_int(ua_ier, UVM_DEFAULT)
    //`uvm_field_int(ua_idr, UVM_DEFAULT)
    //`uvm_field_int(ua_rtrig, UVM_DEFAULT)
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

uart_config uart_cfg;

initial begin
 uart_cfg = uart_config::type_id::create("uart_cfg");
 uart_cfg.print(); 
end

endmodule : test
