/**********************************************************************
  Example 4-19: Using the UVM Factory

  To run:   %  irun -uvmhome $UVM_HOME ex4-19_uvm_factory.sv

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
   `uvm_info("DRIVER", "Driving Transfer", UVM_LOW)
  endtask : run_phase
endclass : driver

class my_project_driver extends driver;
  `uvm_component_utils(my_project_driver)
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  task run_phase(uvm_phase phase);
    `uvm_info("PROJ_DRIVER", "Modifying Transfer", UVM_LOW)
    super.run_phase(phase);
    `uvm_info("PROJ_DRIVER", "Finished Driving Transfer", UVM_LOW)
  endtask : run_phase
endclass : my_project_driver

endpackage : my_pkg

module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
import my_pkg::*;

driver driver1, driver2;

initial begin
  // Create the first agent using the default driver implementation
  driver1 = driver::type_id::create("driver1", null);
  `uvm_info("INFO1", {"driver1.type=", driver1.get_type_name()}, UVM_LOW)
  `uvm_info("INFO1", {"driver.name=", driver1.get_name()}, UVM_LOW)
  // Use the factory to override the second driver
  factory.set_type_override_by_type(driver::get_type(), my_project_driver::get_type());
  // Create the second agent
  driver2 = driver::type_id::create("driver2", null);
  `uvm_info("INFO1", {"driver2.type=", driver2.get_type_name()}, UVM_LOW)
  run_test();
end
endmodule : test
