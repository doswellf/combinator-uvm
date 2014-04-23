/****************************************************************
  Example 4-17: UVM Non-Factory Allocation

  To run:   %  irun -uvm ex4-17_non_factory.sv
  Or:       %  irun -uvmhome $UVM_HOME ex4-17_non_factory.sv
****************************************************************/
package my_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

class driver extends uvm_component;
  `uvm_component_utils(driver)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  task run_phase(uvm_phase phase);
     drive_transfer(); 
  endtask : run_phase

  virtual task drive_transfer();
   `uvm_info("MYINFO", "Begin Driving transfer", UVM_LOW)
   // drive DUT signals
  endtask : drive_transfer

endclass : driver

class agent extends uvm_component; 
  `uvm_component_utils(agent)

`ifndef NEW_DRIVER
  driver my_driver;
`else
  my_project_driver my_driver;
`endif

  function new(string name, uvm_component parent);
    super.new(name, parent);
    my_driver = new("my_driver", this);  // using new()
  endfunction : new

endclass : agent

class my_project_driver extends driver;
  `uvm_component_utils(my_project_driver)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual task drive_transfer();
    super.drive_transfer();
    `uvm_info("MYINFO", "Finished driving transfer", UVM_LOW)
  endtask
endclass : my_project_driver

class my_project_agent extends uvm_component; 
  `uvm_component_utils(my_project_agent)
  my_project_driver my_driver;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    my_driver = new("my_driver", this);  // using new()
  endfunction : new

endclass : my_project_agent

endpackage : my_pkg

module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
import my_pkg::*;

agent my_agent;

initial begin
  my_agent = agent::type_id::create("my_agent", null);
  run_test();
end
endmodule : test
