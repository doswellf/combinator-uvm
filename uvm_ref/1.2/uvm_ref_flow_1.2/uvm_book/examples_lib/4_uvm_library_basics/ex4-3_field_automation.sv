/****************************************************************
  Example 4-3: uvm_object Fields Automation

  To run:   %  irun -uvm ex4-3_field_automation.sv
  OR:       %  irun -uvmhome $UVM_HOME ex4-3_field_automation.sv

  Developers    : Kathleen Meade
  Created       : Dec 6, 2011
  Description   : This file declares a the data item for a simple
                  packet protocol.
  Notes         :
----------------------------------------------------------------
  Copyright Cadence Design Systems (c)2011
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"

//------------------------------------------------------------
// CLASS: packet_header - length, addr
//------------------------------------------------------------
class packet_header extends uvm_object;
  rand bit [5:0]  length;
  rand bit [1:0]  addr;
  // UVM macros for built-in automation - These declarations enable automation
  // of the data_item fields and implement create() and get_type_name()
  `uvm_object_utils_begin(packet_header)
    `uvm_field_int(length, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
  `uvm_object_utils_end
  // Constructor - required syntax for UVM automation and utilities
  function new (string name="packet_header");
     super.new(name);
  endfunction
endclass : packet_header 

typedef enum bit { BAD_PARITY, GOOD_PARITY } parity_e;

//------------------------------------------------------------
// CLASS: simple_packet
//------------------------------------------------------------
//class simple_packet extends uvm_sequence_item;
class simple_packet extends uvm_object;
  // Physical Data
  rand packet_header header;   // packet header class contains addr, length
  rand bit [7:0]  payload [];  // dynamic array
  bit      [7:0]  parity;      // calculated in post_randomize()

  // Control Knobs
  rand parity_e parity_type;
  rand int packet_delay;

  // Default Constraints
  constraint c_default_length { header.length > 0; header.length < 64; }
  constraint c_payload_size   { header.length == payload.size(); }
  constraint c_packet_delay   { packet_delay inside {[0:10]}; }

  // UVM macros for built-in automation - These declarations enable automation
  // of the data_item fields and implement create() and get_type_name()
  `uvm_object_utils_begin(simple_packet)
    `uvm_field_object(header, UVM_DEFAULT)
    `uvm_field_array_int(payload, UVM_DEFAULT)
    `uvm_field_int(parity,      UVM_DEFAULT)
    `uvm_field_enum(parity_e, parity_type, UVM_DEFAULT)
    `uvm_field_int(packet_delay, UVM_DEFAULT | UVM_DEC | UVM_NOCOMPARE)
  `uvm_object_utils_end

  function new (string name = "simple_packet");
    super.new(name);
    header = packet_header::type_id::create("header"); // allocation 
  endfunction : new

  // This method calculates the parity over the header and payload
  function bit [7:0] calc_parity();
    calc_parity = {header.length, header.addr};
    for (int i=0; i<header.length; i++)
      calc_parity = calc_parity ^ payload[i];
  endfunction : calc_parity

  // post_randomize() - calculates parity
  function void post_randomize();
    if (parity_type == GOOD_PARITY)
         parity = calc_parity();
    else do
      parity = $urandom;
    while( parity == calc_parity());
  endfunction : post_randomize

endclass : simple_packet

module test;

simple_packet packet;
//uvm_table_printer printer;

initial begin
  //uvm_default_printer = uvm_default_table_printer;
  //printer = new();
  packet = new("packet");
  //uvm_default_printer.knobs.begin_elements = -1;
  //printer.knobs.begin_elements = -1;
  //printer.knobs.end_elements = 2;
  repeat (3) begin
    void'(packet.randomize());
    //packet.print(printer);
    packet.print();
  end
end
endmodule : test
