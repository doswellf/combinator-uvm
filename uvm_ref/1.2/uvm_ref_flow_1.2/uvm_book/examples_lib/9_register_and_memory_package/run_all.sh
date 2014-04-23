#!/bin/sh

#  Example 9-1: Register to APB Adapter for the UART Controller Testbench
irun -uvm -incdir ../7_simple_testbench_integration/apb ex9-1_reg_to_apb_adapter.sv -log irun_ex9_1.log

#  Example 9-2: UART Controller Line Control Register XML Description
#  Example 9-3: UART Controller XML Description for the Reg File, Address Map
$IREG_GEN/bin/iregGen -i ex9-3_ua_simple_regs.xml -nc -uvm11a

#  Example 9-4: UART Controller Line Control Register - SystemVerilog
#  Example 9-5: UART Controller Reg File, Address Map - SystemVerilog
irun -uvm ex9-5_ua_simple_regs.sv -log irun_ex9_5.log

#  Generate UART Controller Register File
$IREG_GEN/bin/iregGen -i uart_ctrl_regs.xml -uvm11a -o uart_ctrl_regs.sv

#  Example 9-6: Extending UART Controller Register File to disable checks
irun -uvm ex9-6_extend_rf.sv -log irun_ex9_6.log

# Example 9-7: UART Controller Module UVC with Register Layer Additions
# Example 9-8: UART Controller Testbench with Register Model Components
# Example 9-9: Base Register Sequence for UART Controller Testbench
# Example 9-10: UART Controller Register Configuration Sequence
# Example 9-11: Using the UVM Built-in Sequences
# Example 9-12: Multi-register Sequence Example
# Example 9-13: iregGen Generated Covergroup


### Check Results ###
errors=0;
for file in `ls irun_ex9_*.log`
do
if (grep "*E," $file) then
  echo "--------------------------------------------------"
  echo " COMPILE/ELAB/SIM ERRORS - Check $file for details "
  echo "--------------------------------------------------"
  echo " TEST FAILED - Check $file file for details."
  let errors="errors+1"
else
  #if (grep "UVM_ERROR" $file | grep -v " :    0" ) then
  if (grep -e "UVM_\(FATAL\|ERROR\)" $file | grep -v " :    0" ) then
    echo "--------------------------------------------------"
    echo " UVM_FATAL/UVM_ERROR messages found - Check $file for details "
    echo "--------------------------------------------------"
    echo " TEST FAILED - Check $file file for details."
    let errors="errors+1"
  else
    echo "--------------------------------------------------"
    echo " TEST PASSED - $file "
  fi
fi
echo "--------------------------------------------------"
done
echo " TOTAL ERRORS = $errors"
echo "--------------------------------------------------"
