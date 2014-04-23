/*
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
Standalone test file to test generated register definition file
 To simlulate : 
      'irun +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv \
          /export/home/meade/proj/UVM/book/soc_ex/uart_ctrl/ipxact/simple_test.sv \
          +incdir+$UVM_RGM_HOME/sv \
          $UVM_RGM_HOME/dpi/rgm_set_hdl.c'
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
*/

module test();

  import uvm_pkg::*;
  import uvm_rgm_pkg::*;
  `include "uvm_macros.svh"
  `include "uvm_rgm_defines.sv"
  `include "./uart_ctrl_regs.sv"

  uart_ctrl_reg_db uart_ctrl_reg_db_inst;
  initial
  begin
    uvm_rgm_address_map m[$];
    // Set printer to tree printer
    uvm_default_printer=uvm_default_tree_printer;
    uart_ctrl_reg_db_inst=uart_ctrl_reg_db::type_id::create("uart_ctrl_reg_db_inst", null);
    uart_ctrl_reg_db_inst.build();
    m=uart_ctrl_reg_db_inst.addr_map;
    // Set the print detail to required verbosity
    // foreach(m[i]) m[i].set_print_detail_hier(PRINT_SHORT);
    foreach(m[i]) m[i].set_print_detail_hier(PRINT_FULL);
    uart_ctrl_reg_db_inst.reset("HARD");
    // Print register data-base hierachy
    uart_ctrl_reg_db_inst.print();
    $finish;
  end
endmodule
