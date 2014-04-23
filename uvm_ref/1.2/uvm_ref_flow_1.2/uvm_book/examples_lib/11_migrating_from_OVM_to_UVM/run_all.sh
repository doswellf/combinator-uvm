#!/bin/sh

#  Example 11-1ea: UVM Testbench Migration - UVM1.0 EA
irun -uvm ex11-1_UVMea.sv -log irun_ex11_UVMea.log

#  Example 11-1ea: UVM Testbench Migration - UVM1.0 Migrated
irun -uvm ex11-1_UVM.sv -log irun_ex11_UVM.log

### Check Results ###
errors=0;
for file in `ls irun_ex11_*.log`
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
