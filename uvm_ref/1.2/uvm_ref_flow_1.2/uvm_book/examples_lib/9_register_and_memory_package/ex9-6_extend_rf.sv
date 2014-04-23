/* Example 9-6:  Extending the UART Controller Register File to Disable Checks

 Set IREG_GEN to $IES_INSTALL_DIR/tools/methodology/iregGen
 Generated rdb.sv by executing:
   % $IREG_GEN/bin/iregGen  -i uart_ctrl_regs.xml -uvm11a -o uart_ctrl_regs.sv

 Run the testcase:
   %  irun -uvm ex9-6_extend_rf.sv
*/
//////////////////////////////////////////////////////////////////////
// Register definition 
////////////////////////////////////////////////////////////////////// 
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "uart_ctrl_regs.sv"
class nocheck_rf_c extends uart_ctrl_rf_c;

  virtual function void build();
    super.build();
    ua_int_id.priority_bit.set_compare(UVM_NO_CHECK);
  endfunction

  `uvm_object_utils(nocheck_rf_c)
  function new(input string name="rf");
    super.new(name);
  endfunction : new
endclass : nocheck_rf_c
