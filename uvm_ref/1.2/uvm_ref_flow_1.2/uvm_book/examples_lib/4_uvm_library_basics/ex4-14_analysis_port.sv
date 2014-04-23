/****************************************************************
  Example 4-14: Collector with an Analysis Port

  To run:   %  irun -uvm ex4-14_analysis_port.sv
  Or        %  irun -uvmhome $UVM_HOME ex4-14_analysis_port.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "simple_packet.sv"

class packet_collector extends uvm_component;

  uvm_analysis_port #(simple_packet) analysis_port;

  `uvm_component_utils(packet_collector)
  function new(string name, uvm_component parent);
    super.new(name, parent);
    analysis_port = new("analysis_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    simple_packet packet = new("packet");
    // reassemble packet here from lower level protocol
    analysis_port.write(packet);  // write the collected packet to the port
  endtask  : run_phase

endclass : packet_collector
