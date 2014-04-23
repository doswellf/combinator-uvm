#!/bin/sh

## Check Results
rm FAIL.list
errors=0;
allfiles=0;
for file in `ls ./irun_*.log`
do
let allfiles="allfiles+1"
if (grep "*E," $file) then
  echo "--------------------------------------------------"
  echo " COMPILE/ELAB/SIM ERRORS - Check $file for details "
  echo "--------------------------------------------------"
  echo " TEST FAILED - Check $file file for details."
  let errors="errors+1"
  `ls $file >> FAIL.list`
else
  if  (grep -e "UVM_\(FATAL\|ERROR\)" $file | grep -v " :    0" ) then
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
echo " TOTAL TESTS = $allfiles"
echo " TOTAL ERRORS = $errors  - (see ./FAIL.list)"
echo "--------------------------------------------------"
