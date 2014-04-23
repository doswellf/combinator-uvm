/**************************************************************************
  Example 5-4: APB Master Driver Definition

  To run:   %  irun -uvm ex5-4_apb_master_driver.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-4_apb_master_driver.sv
**************************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sv/apb_if.sv"
`include "sv/apb_transfer.sv"

//------------------------------------------------------------------------------
// CLASS: apb_driver
//------------------------------------------------------------------------------
class apb_master_driver extends uvm_driver #(apb_transfer);

  // The virtual interface used to drive and view HDL signals.
  virtual apb_if vif;
  
  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils(apb_master_driver)

  // Constructor which calls super.new() with appropriate parameters.
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  extern virtual function void connect_phase (uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
  extern virtual protected task get_and_drive();
  extern virtual protected task reset_signals();
  extern virtual protected task drive_transfer(apb_transfer trans);

endclass : apb_master_driver

function void apb_master_driver::connect_phase(uvm_phase phase);
  // add logic to make the virtual interface connection
endfunction : connect_phase

// Declaration of the run_phase() phase method.  This method
// fork/join_none's the get_and_drive() and reset_signals() methods.
task apb_master_driver::run_phase(uvm_phase phase);
  fork
    get_and_drive();
    reset_signals();
  join
endtask : run_phase

// Task thats manages the interaction between the master
// sequence sequencer
task apb_master_driver::get_and_drive();
  forever begin
    // Get the next data item from the sequencer (may block)
    seq_item_port.get_next_item(req);
    drive_transfer(req);
    seq_item_port.item_done(req);
  end
endtask : get_and_drive

// Task that is fork/join_none'ed in the run phase in order to drive all 
// signals to reset state at the appropriate time.
task apb_master_driver::reset_signals();
  forever begin
    @(negedge vif.presetn);
    `uvm_info("APB_MASTER_DRIVER", "Reset observed", UVM_MEDIUM)
    vif.paddr     <= 'h0;
    vif.pwdata    <= 'h0;
    vif.pwrite    <= 'b0;
    vif.psel      <= 'b0;
    vif.penable   <= 'b0;
  end
endtask : reset_signals

// Task that is called by another component (typically the driver component) 
// when an item is ready to be sent.  This task drives all phases of 
// transfer.
task apb_master_driver::drive_transfer (apb_transfer trans);
    `uvm_info("APB_MASTER_DRIVER", $sformatf("APB Finished Driving Transfer \n%s", trans.sprint()), UVM_MEDIUM)
endtask : drive_transfer
