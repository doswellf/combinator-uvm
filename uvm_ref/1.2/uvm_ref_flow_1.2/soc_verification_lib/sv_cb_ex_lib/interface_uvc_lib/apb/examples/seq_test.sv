//To RUN:  %  irun -incdir $UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv seq_test.sv
module seq_test;

import uvm_pkg::*;
`include "uvm_macros.svh"

class alu_sequence_item extends uvm_sequence_item;

 rand logic [7:0] data;
 
 `uvm_object_utils_begin(alu_sequence_item)
   `uvm_field_int(data, UVM_DEFAULT)
 `uvm_object_utils_end

 //function new(string name="alu_sequence_item");
 function new(string name="");
   super.new(name);
 endfunction : new

endclass : alu_sequence_item

class alu_sequencer extends uvm_sequencer #(alu_sequence_item, alu_sequence_item);

`uvm_component_utils(alu_sequencer)

function new(string name="", uvm_component parent=null);
   super.new(name, parent);
endfunction 

function void build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

endclass : alu_sequencer

endmodule : seq_test
