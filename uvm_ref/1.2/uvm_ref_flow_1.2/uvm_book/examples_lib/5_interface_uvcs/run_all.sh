#!/bin/sh

#  Example 5-1: APB Transfer
irun -uvm ex5-1_apb_transfer.sv -log irun_ex5_1.log

#  Example 5-2: Defining a Transaction Control Field
irun -uvm ex5-2_apb_transfer1.sv -log irun_ex5_2.log

#  Example 5-3: Test for the apb_transfer Data Item
irun -uvm ex5-3_apb_transfer_test.sv -log irun_ex5_3.log

#  Example 5-4: APB Master Driver Definition
irun -uvm ex5-4_apb_master_driver.sv -log irun_ex5_4.log

#  Example 5-5: APB Interface Definition
irun  ex5-5_apb_interface.sv -log irun_ex5_5.log

#  Example 5-6: Virtual Interface Usage - APB Master Driver
irun -uvm ex5-6_apb_master_driver.sv

#  Example 5-6a: Configuring the virtual interface
irun -uvm ex5-6a_configure_vif.sv -log irun_ex5_6a.log

#  Example 5-6b: Simple APB Interface/Driver Test
irun -uvm ex5-6b_test_driver.sv -log irun_ex5_6b.log

#  Example 5-7: Non-UVM Generator Code
irun -uvm ex5-7_generator.sv -log irun_ex5_7.log

#  Example 5-8: APB Master Sequencer
irun -uvm ex5-8_apb_master_sequencer.sv -log irun_ex5_8.log

#  Example: Simple Driver/Sequencer interaction
irun -uvm ex5-8a_driver_sequencer.sv -log irun_ex5_8a.log

#  Example 5-9: Simple Driver for Pipeline Protocol
#  KATHLEEN - FIX THIS!!!
irun -uvm ex5-9_simple_pipe_driver.sv -log irun_ex5_9.log

#  Example 5-10: APB Collector
irun -uvm ex5-10_apb_collector.sv -log irun_ex5_10.log

#  Example 5-11: APB Monitor
irun -uvm ex5-11_apb_monitor.sv -log irun_ex5_11.log

#  Example 5-12: APB Master Agent
irun -uvm ex5-12_apb_master_agent.sv -log irun_ex5_12.log

#  Example: Simple APB Agent Test
irun -uvm ex5-12a_test_agent.sv -log irun_ex5_12a.log

#  Example 5-13: Configuring the APB UVC in the build() Method
irun -uvm ex5-13_apb_env.sv -log irun_ex5_13.log

#  Example: Simple APB Env Test
irun -uvm ex5-13a_test_env.sv -log irun_ex5_13a.log

#  Example 5-14: APB Configuration Classes (slave, master and env config)
irun -uvm ex5-14_apb_config.sv -log irun_ex5_14.log

#  Example 5-15: Configuring the APB UVC in the build_phase method
irun -uvm ex5-15_apb_env_build.sv -log irun_ex5_15.log

#  Example 5-16: Extending the Default APB Configuration
irun -uvm ex5-16_demo_apb_config.sv -log irun_ex5_16.log

#  Example 5-17: Testbench build() overrides the default APB configuration
irun -uvm ex5-17_apb_tb_build.sv -log irun_ex5_17.log

#  Example 5-18: APB Simple Sequence
irun -uvm ex5-18_apb_transfer_seq.sv -log irun_ex5_18.log

#  Example 5-19: APB Multiple Transfer Sequence
irun -uvm ex5-19_multi_transfer_seq.sv -log irun_ex5_19.log

#  Example 5-20: APB Sequence with Randomizable Parameters and Constraints
irun -uvm ex5-20_sequence_w_params.sv -log irun_ex5_20.log

#  Example 5-21: APB Traffic Sequence
irun -uvm ex5-21_apb_traffic_seq.sv -log irun_ex5_21.log

#  Example 5-22: UVM Sequence Library Usage
irun -uvm ex5-22_sequence_library.sv -log irun_ex5_22.log

#  Example 5-23: APB Sequence Incorporating End of Test
irun -uvm ex5-23_apb_read_block_seq.sv -log irun_ex5_23.log

#  Example 5-24: APB Master Base Sequence Incorporating Objection Mechanism
irun -uvm ex5-24_apb_master_base_seq.sv -log irun_ex5_24.log

#  Example 5-25: APB Sequence Derived from Base Sequence
irun -uvm ex5-25_apb_read_byte_seq.sv -log irun_ex5_25.log


### Check Results ###
errors=0;
for file in `ls irun_ex5_*.log`
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
