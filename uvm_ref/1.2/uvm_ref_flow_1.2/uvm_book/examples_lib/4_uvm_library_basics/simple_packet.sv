/*******************************************************************
  File: simple_packet.sv
*******************************************************************/
class simple_packet extends uvm_sequence_item;
  rand int src_addr;
  rand int dst_addr;
  rand byte unsigned data[];
 
  // Constraints
  constraint c_data { data.size inside { 4, 8, 12, 16 }; }

  `uvm_object_utils_begin(simple_packet)
     `uvm_field_int(src_addr, UVM_DEFAULT)
     `uvm_field_int(dst_addr, UVM_DEFAULT)
     `uvm_field_array_int(data, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name="simple_packet");
    super.new(name);
  endfunction : new

  function void transform1();
    // transform function #1 for scoreboard
  endfunction : transform1

  function void transform2();
    // transform function #2 for scoreboard
  endfunction : transform2
  
endclass : simple_packet
