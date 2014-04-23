#!/bin/sh

#  Example 3-1: SystemVerilog Class Example
irun ex3-1_class_example.sv -log irun_ex3_1.log

#  Example 3-2: Generalization and Inheritance
irun ex3-2_inheritance.sv -log irun_ex3_2.log

#  Example 3-3: Inheritance and Polymorphism
irun ex3-3_polymorphism.sv -log irun_ex3_3.log

#  Example 3-4: Downcast
irun ex3-4_downcast.sv -log irun_ex3_4.log

#  Example 3-5: Static Methods and Attributes
irun ex3-5_static_methods.sv -log irun_ex3_5.log

#  Example 3-6 : Parameterized Class With Static Field
irun ex3-6_param_class.sv -log irun_ex3_6.log

#  Example 3-7: Parameterized Class Using Base Class for Static Field
irun ex3-7_param_class_base.sv -log irun_ex3_7.log

#  Example : SystemVerilog Packages and Namespace
irun ex3-8_packages.sv -log irun_ex3_8.log

#  Example 3-9 : Packages and Namespace - no collision
irun ex3-9_packages.sv -log irun_ex3_9.log


for file in `ls irun_ex3_*.log`
do
if (grep "*E," $file) then
  echo "--------------------------------------------------"
  echo " COMPILE/ELAB/SIM ERRORS - Check $file for details "
  echo "--------------------------------------------------"
  echo " TEST FAILED - Check $file file for details."
else
  echo "--------------------------------------------------"
  echo " TEST PASSED - $file "
fi
echo "--------------------------------------------------"
done
