/****************************************************************
  Example 4-15: Component with an Analysis Import

  To run:   %  irun -uvm ex4-15_analysis_imp.sv

  Or:       %  irun -uvmhome $UVM_HOME ex4-15_analysis_imp.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "simple_packet.sv"

class packet_checker extends uvm_component;

  uvm_analysis_imp #(simple_packet, packet_checker) analysis_export;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    analysis_export = new("analysis_export", this);
  endfunction
  
  `uvm_component_utils(packet_checker)

  function void write(simple_packet packet);
    // check the packet here
  endfunction : write

endclass : packet_checker
