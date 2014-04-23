/*******************************************************************
  Example : Transaction from a Producer to a Consumer using get

  To run:   %  irun -uvm  ex4-10_tlm_get.sv
*******************************************************************/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "simple_packet.sv"

class producer_2 extends uvm_component;
  uvm_blocking_get_imp #(simple_packet, producer_2) get_export;

  `uvm_component_utils(producer_2)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    get_export = new("get_export", this);
  endfunction : new

  task get(output simple_packet packet);
    simple_packet packet_temp;
    packet_temp = simple_packet::type_id::create("packet");
    void'(packet_temp.randomize());
    packet = packet_temp;
  endtask : get

endclass : producer_2

class consumer_2 extends uvm_component;
  uvm_blocking_get_port #(simple_packet) get_port;

  `uvm_component_utils(consumer_2)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    get_port = new("get_port", this);
  endfunction : new

  task run_phase(uvm_phase phase);
    simple_packet packet; 
    get_port.get(packet);
    packet.print();
  endtask : run_phase
endclass : consumer_2

class parent_comp extends uvm_component;

  producer_2 producer_inst;
  consumer_2 consumer_inst;

  `uvm_component_utils(parent_comp)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    producer_inst = producer_2::type_id::create("producer_inst", null);
    consumer_inst = consumer_2::type_id::create("consumer_inst", null);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    consumer_inst.get_port.connect(producer_inst.get_export);
  endfunction : connect_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    this.print();
  endfunction : end_of_elaboration_phase

endclass : parent_comp

parent_comp parent;

initial begin
  parent = parent_comp::type_id::create("parent", null);
  run_test();
end

endmodule : test
