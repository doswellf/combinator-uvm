/*-------------------------------------------------------------------------
File name   : ahb_user_monitor.sv
Title       : 
Project     :
Created     :
Description : 
Notes       :
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

class ahb_monitor extends ahb_pkg::ahb_master_monitor;
   
  uvm_analysis_port #(ahb_pkg::ahb_transfer) ahb_transfer_out;

  `uvm_component_utils(ahb_monitor)

  function new (string name = "ahb_monitor", uvm_component parent);
    super.new(name, parent);
    ahb_transfer_out = new("ahb_transfer_out", this);
  endfunction

  virtual protected task print_transfers();
    uvm_object obj;
     `uvm_info("USR_MONITOR", $sformatf("print_transfers called"), UVM_MEDIUM)
		
	  // ---------------------
	  // ---| transfer ended |---
	  // ---------------------
	  forever begin
	    // Wait until transfer ended, and put the ended transfer in 'obj'.
	    @transaction_ended; 

	    // Transaction recording
	    trans_collected.enable_recording("AHB transfers monitor");
	    void'(trans_collected.begin_tr());
	    trans_collected.end_tr();

	    // Display a message about the transfer that just ended
 	    `uvm_info("USR_MONITOR", $sformatf(" %s to %0h with data %0h has ended", trans_collected.direction.name(), trans_collected.address, trans_collected.data), UVM_MEDIUM)
      ahb_transfer_out.write(trans_collected);
	  end
  endtask

   // run() task is called automatically
   virtual task run_phase(uvm_phase phase);
     `uvm_info("USR_MONITOR", $sformatf("run started"), UVM_LOW)
     super.run_phase(phase);
     print_transfers(); 
   endtask

endclass

