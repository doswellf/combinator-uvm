/**********************************************************************
  Example 4-4: UVM Object Automation

  To run:   %  irun -uvm ex4-4_object_automation.sv
  OR:       %  irun -uvmhome $UVM_HOME ex4-4_object_automation.sv
**********************************************************************/
package apb_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `include "apb_transfer.sv"
  // Other files for APB UVC go here
endpackage : apb_pkg

module automation_example;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import apb_pkg::*;

  apb_transfer my_xfer, tx1, tx2, tx3;

  initial begin
    my_xfer = apb_transfer::type_id::create("my_xfer");
    if (!my_xfer.randomize())
      `uvm_fatal("RANDFAIL", "can not randomize my_xfer")
    tx1 = my_xfer;              // tx1 and my_xfer share the same memory
    tx2 = apb_transfer::type_id::create("tx2");
    tx2.copy(tx1);              // copies fields from tx1 to tx2
    $cast(tx3, tx1.clone());    // creates a new apb_transfer and copy all
                                // fields from tx1 to tx3
    if (!tx3.compare(tx2))
      `uvm_error("CompareFailed", "The comparison failed")
    my_xfer.print();            // Prints my_xfer in a table format
    my_xfer.print(uvm_default_tree_printer);  // Prints in "tree" format
    my_xfer.print(uvm_default_line_printer);  // Prints in "line" format
  end

endmodule : automation_example
