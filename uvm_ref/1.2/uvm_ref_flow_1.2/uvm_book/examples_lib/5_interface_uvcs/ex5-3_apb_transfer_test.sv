/**************************************************************************
  Example 5-3: Test for the apb_transfer Data Item

  To run:   %  irun -uvmhome $UVM_HOME ex5-3_apb_transfer_test.sv

  Use -svseed random command line option to get different random results
  for each run
**************************************************************************/
// Create a package for the APB UVC
package apb_pkg;
// Import the UVM library and include the UVM macros
import uvm_pkg::*;
`include "uvm_macros.svh"

// Include all files for the APB UVC
`include "sv/apb_transfer.sv"
// Other files go here
endpackage : apb_pkg

module test;
// Import the UVM library and include the UVM macros
import uvm_pkg::*;
`include "uvm_macros.svh"

import apb_pkg::*;   // Import the APB UVC Package

apb_transfer my_xfer;

initial begin
  my_xfer = apb_transfer::type_id::create("my_xfer");
  repeat (5) begin
    if (!my_xfer.randomize())
      `uvm_fatal("RANDFAIL", "Can not randomize my_xfer")
    my_xfer.print();
  end
  // Now randomize with additional inline constraints
  if (!my_xfer.randomize() with {addr inside {['h0000:'hFFFF]}; 
                                 direction == APB_WRITE; })
      `uvm_fatal("RANDFAIL", "Can not randomize my_xfer")
  my_xfer.print();
end

endmodule : test
