/**********************************************************************
  Example 4-18: Using the UVM Factory

  To run:   %  irun -uvmhome $UVM_HOME ex4-18_uvm_factory.sv

  Notes:  Use the following syntax to override the driver:
          (before creating the driver)

          factory.set_type_override_by_type(driver::get_type(),
                                    my_project_driver::get_type());
**********************************************************************/
package my_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

class driver extends uvm_component;
  `uvm_component_utils(driver)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  task run_phase(uvm_phase phase);
     // 
     drive_transfer(); 
  endtask : run_phase

  virtual task drive_transfer();
   `uvm_info("MYINFO", "Begin Driving transfer", UVM_LOW)
   // drive DUT signals
  endtask : drive_transfer

endclass : driver

class agent extends uvm_component; 
  `uvm_component_utils(agent)
  driver my_driver;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    my_driver = driver::type_id::create("my_driver", this);
  endfunction : new

endclass : agent

class my_project_driver extends driver;
  `uvm_component_utils(my_project_driver)

  virtual task drive_transfer();
    super.drive_transfer();
    `uvm_info("MYINFO", "Finished Driving Transfer", UVM_LOW)
  endtask
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
endclass : my_project_driver

endpackage : my_pkg

module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
import my_pkg::*;

agent my_agent;

initial begin
  // factory is a field in the UVM package (uvm_pkg)
  factory.set_type_override_by_type(driver::get_type(), my_project_driver::get_type());
  // Create the agent
  my_agent = agent::type_id::create("my_agent", null);
  // Run the uvm_phases
  run_test();
end
endmodule : test
