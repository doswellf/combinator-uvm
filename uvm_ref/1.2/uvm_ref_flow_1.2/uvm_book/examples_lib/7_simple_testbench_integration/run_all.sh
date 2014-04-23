#!/bin/sh

#  Example 7-1: UART Controller Testbench
irun -f run.f ex7-1_uart_ctrl_tb.sv -log irun_ex7_1.log

# No test required for the examples below:
#  Example 7-2: UART Controller Testbench - Build Phase
#  Example 7-3: UART Controller Testbench - Connect Phase
#  Example 7-4: UART Controller Virtual Sequencer

#  Example 7-5: APB Configuration Class
irun -uvm ex7-5_apb_config.sv -log irun_ex7_5.log

#  Example 7-6: UART Configuration Class
irun -uvm ex7-6_uart_config.sv -log irun_ex7_6.log

#  Example 7-7: UART Controller Base Test
#  Example 7-8: UART Controller Test Derived from the Base Test

#  Example 7-9: UART Frame Data Item
irun -uvm ex7-9_uart_frame.sv -svseed random -log irun_ex7_9.log

#  Example 7-10: UART Controller Data Item Override Test

#  Example 7-11: UART Retry Sequence
irun -uvm -incdir ./uart/sv ./uart/sv/uart_pkg.sv ex7-11_retry_seq.sv -log irun_ex7_11.log

#  Example 7-12: UART Nested Retry Sequence
irun -uvm -incdir ./uart/sv ./uart/sv/uart_pkg.sv ex7-12_rand_retry_seq.sv -log irun_ex7_12.log

#  Example 7-13: Directed Test - needs work
irun -f run.f ex7-13_directed_test.sv -log irun_ex7_13.log

#  Example 7-14: Base Virtual Sequence with Objection Mechanism
#  Example 7-15: UART Controller Virtual Sequence

#####################################################
##  THESE TWO TESTS ARE SIMPLE TB TESTS - NO DUT   ##
#####################################################

#  UART Controller Test without Virtual Sequence (NO DUT)
irun -f run.f tb/uart_ctrl_test.sv +UVM_TESTNAME=u2a_a2u_rand_test -log irun_ex7_test1.log

#  UART Controller Test with Virtual Sequence (NO DUT)
irun -f run.f tb/uart_ctrl_test.sv +UVM_TESTNAME=u2a_a2u_vseq_test -log irun_ex7_test2.log

### Check Results ###
errors=0;
for file in `ls irun_ex7_*.log`
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
