/**********************************************************************
  Example 4-22: Simple Objection Mechanism

  To run:   %  irun -uvm ex4-22_simple_objections.sv
  OR:       %  irun -uvmhome $UVM_HOME ex4-22_simple_objections.sv

OPTIONALLY - run with +UVM_OBJECTION_TRACE to get all the trace 
  information for the objections
**********************************************************************/
`timescale 1ns/1ns
package my_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

class master_comp extends uvm_component;
  `uvm_component_utils(master_comp)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  task run_phase (uvm_phase phase);
    `uvm_info("MASTER", "run_phase: Executing.", UVM_LOW)
    phase.raise_objection(this, "MASTER raises an objection");
    repeat (2) #5 phase.raise_objection(this, "MASTER raises an objection");
    repeat (2) #10 phase.drop_objection(this, "MASTER drops an objection");
    #70 phase.drop_objection(this, "MASTER drops an objection");
  endtask : run_phase
endclass : master_comp

class testbench_comp extends uvm_component;
  master_comp master;
  `uvm_component_utils(testbench_comp)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    master = master_comp::type_id::create("master", this);
  endfunction : build_phase

  task run_phase (uvm_phase phase);
    uvm_objection objection;
    `uvm_info("TBENCH", "run_phase: Executing.", UVM_LOW)
    objection = phase.get_objection();
    phase.raise_objection(this, "TBENCH raises 2 objections", 2);
    phase.phase_done.set_drain_time(this, 1000);
    #20 objection.display_objections();
    `uvm_info("TBENCH", $sformatf("get_objection_count=%0d",
               objection.get_objection_count(this)), UVM_LOW);
    `uvm_info("TBENCH", $sformatf("get_objection_total=%0d",
               objection.get_objection_total), UVM_LOW);
    repeat (2)
      #10 phase.drop_objection(this, "TBENCH drops an objection");
  endtask : run_phase

  task all_dropped(uvm_objection objection, uvm_object source_obj, string description, int count);
    if (objection == uvm_test_done) begin
      //repeat (15) @(posedge vif.pclock);
      #100
        objection.clear();
    end
  endtask

endclass : testbench_comp
endpackage : my_pkg

module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

import my_pkg::*;

testbench_comp testbench;

initial begin
// Create components
  testbench = testbench_comp::type_id::create("testbench", null);
// Start UVM Phases
  run_test();
end

endmodule : test
