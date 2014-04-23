#!/bin/sh

#  Example 8-1: Using p_sequencer in a sequence
irun -uvm -incdir ../7_simple_testbench_integration/apb ex8-1_interrupt.sv -log irun_ex8_1.log

#  Example 8-2: Handling interrupts using Sequences
irun -uvm -incdir ../7_simple_testbench_integration/apb ex8-2_interrupt_sequence.sv -log irun_ex8_2.log

#  Example 8-2a: Sequence Layering in One Sequencer
irun -uvm ex8-2a_single_layer_arch.sv -log irun_ex8_2a.log

#  Example 8-3: Layered Sequencers
irun -uvm ex8-3_layered_sequencers.sv -log irun_ex8_3.log

#  Example 8-4: Layered Sequences
irun -uvm ex8-4_layered_sequences.sv -log irun_ex8_4.log

### Check Results ###
errors=0;
for file in `ls irun_ex8_*.log`
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
