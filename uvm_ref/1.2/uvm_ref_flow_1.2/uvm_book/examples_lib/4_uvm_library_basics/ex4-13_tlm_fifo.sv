/*******************************************************************
  Example 4-13: TLM FIFO Usage

  To run:   %  irun -uvm  ex4-13_tlm_fifo.sv
  Or:       %  irun -uvmhome $UVM_HOME ex4-13_tlm_fifo.sv
*******************************************************************/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "simple_packet.sv"

typedef class producer;
typedef class consumer_2;

class producer_consumer_2 extends uvm_component;
  producer   producer_inst;
  consumer_2 consumer_inst;

  uvm_tlm_fifo #(simple_packet) fifo_inst;  // fifo stores simple packets
 
  `uvm_component_utils(producer_consumer_2)

  function new(string name, uvm_component parent);
    super.new(name, parent);
    producer_inst = new("producer_inst", this);
    consumer_inst = new("consumer_inst", this);
    fifo_inst = new("fifo_inst", this, 16);  // set fifo depth to 16
  endfunction : new

  virtual function void connect_phase(uvm_phase phase);
    producer_inst.put_port.connect(fifo_inst.put_export);
    consumer_inst.get_port.connect(fifo_inst.get_export);
  endfunction : connect_phase

  task run_phase(uvm_phase phase);
     this.print();
  endtask : run_phase

endclass : producer_consumer_2

class producer extends uvm_component;
  uvm_blocking_put_port #(simple_packet) put_port;

  `uvm_component_utils(producer)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    put_port = new("put_port", this);
  endfunction : new

  virtual task run_phase(uvm_phase phase);
    simple_packet producer_p;
    producer_p = simple_packet::type_id::create("producer_p");
    void'(producer_p.randomize());
    put_port.put(producer_p);
  endtask : run_phase

endclass : producer

class consumer_2 extends uvm_component;
  uvm_blocking_get_port #(simple_packet) get_port;

  `uvm_component_utils(consumer_2)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    get_port = new("get_port", this);
  endfunction : new

  task run_phase(uvm_phase phase);
    simple_packet consumer_p; 
    get_port.get(consumer_p);
    consumer_p.print();
  endtask : run_phase

endclass : consumer_2

producer_consumer_2 pc;

initial begin
  pc = producer_consumer_2::type_id::create("pc", null);
  run_test();
end

endmodule : test
