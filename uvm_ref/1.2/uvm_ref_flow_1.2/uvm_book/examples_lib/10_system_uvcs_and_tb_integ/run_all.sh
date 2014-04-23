#!/bin/sh

#Chapter 10: System UVCs and Testbench Integration

# Example 10-1: UART Controller Module Monitor
# Example 10-2: UART Controller Monitor build_phase() and connect_phase()
# Example 10-3: UART Controller Module UVC
# Example 10-4: UART Configuration Class
irun -uvm ex10-4_uart_config.sv -log irun_ex10_4.log
# Example 10-5: UART Controller Configuration Class
irun -uvm ex10-5_uart_ctrl_config.sv -log irun_ex10_5.log
# Example 10-6: UART Controller Testbench
#irun -f run.f ex10-6_uart_ctrl_tb.sv -log irun_ex10_6.log
# Example 10-7: UART Controller Base Virtual Sequence
# Example 10-8: UART Controller Virtual Sequence
# Example 10-9: Module UVC DUT Coverage
# Example 10-10: Module UVC Performance-Related Coverage
# Example 10-11: Configuration Sequence with Configurable Backdoor Access

### Check Results ###
errors=0;
for file in `ls irun_ex10_*.log`
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
