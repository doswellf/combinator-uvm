#!/bin/sh

#  Example: ex4-0_hello_world.sv
irun -uvm ex4-0_hello_world.sv -log irun_ex4_0.log

#  Example 4-1: Non-UVM Class Definition
irun ex4-1_apb_transfer_no_uvm.sv -log irun_ex4_1.log

#  Example 4-2: APB Transfer Derived from uvm_object
irun -uvm ex4-2_apb_transfer.sv -log irun_ex4_2.log

#  Example 4-3: uvm_object Fields Automation
irun -uvm ex4-3_field_automation.sv -log irun_ex4_3.log

#  Example 4-4: UVM Object Automation
irun -uvm ex4-4_object_automation.sv -log irun_ex4_4.log

#  Example 4-5: uvm_component Simulation Phases and Hierarchy Methods
irun -uvm ex4-5_sim_phases.sv -log irun_ex4_5.log

#  Example 4-6: Configuration Mechanism (no configuration)
irun -uvm ex4-6_default_config.sv -log irun_ex4_6.log

#  Example 4-7: Configuration Mechanism
irun -uvm ex4-7_config.sv -log irun_ex4_7.log

# Example 4-8: Configuration Mechanism for Coverage
irun -uvm -coverage u ex4-8_config_coverage.sv -log irun_ex4_8.log

#  Example 4-8a: Configuration Mechanism - Checking using exists()
irun -uvm ex4-8a_check_config.sv -log irun_should_uvm-error_ex4_8a.log

#  Example 4-9: Transaction from a Producer to a Consumer using put
irun -uvm ex4-9_tlm_put.sv -log irun_ex4_9.log

#  Example 4-10: Transaction from a Producer to a Consumer using get
irun -uvm  ex4-10_tlm_get.sv -log irun_ex4_10.log

#  Example 4-11: Connecting a Child Port to a Parent Port
irun -uvm ex4-11_tlm_port_connect.sv -log irun_ex4_11.log

#  Example 4-12: Connecting a Child Export to a Parent Export
irun -uvm ex4-12_tlm_export_connect.sv -log irun_ex4_12.log

#  Example 4-13: TLM FIFO Usage
irun -uvm  ex4-13_tlm_fifo.sv -log irun_ex4_13.log

#  Example 4-14: Collector with an Analysis Port
irun -uvm ex4-14_analysis_port.sv -log irun_ex4_14.log

#  Example 4-15: Component with an Analysis Import
irun -uvm ex4-15_analysis_imp.sv -log irun_ex4_15.log

#  Example 4-16: Usage of uvm_analysis_imp_decl macros
irun -uvm ex4-16_decl_macros.sv -log irun_ex4_16.log

#  Example 4-17: UVM Non-Factory Allocation
irun -uvm ex4-17_non_factory.sv -log irun_ex4_17.log

#  Example 4-18: Using the UVM Factory
irun -uvm ex4-18_uvm_factory.sv -log irun_ex4_18.log

#  Example 4-19: Using the UVM Factory
irun -uvm ex4-19_uvm_factory.sv -log irun_ex4_19.log

#  Example 4-20: UVM Message Macros within Modules
irun -uvm ex4-20_messages.sv -log irun_ex4_20.log

#  Example 4-21: Message Callback Usage
irun -uvm message_callback_test.sv -log irun_should_uvm_error_ex4_21.log

#  Example 4-21: Message Callback Usage
irun -uvm ex4-21_message_callback.sv -log irun_should_uvm_error_ex4_21x.log

#  Example 4-21a: Callbacks Example
irun -uvm  ex4-21a_callbacks.sv -log irun_ex4_21a.log

#  Example 4-21b: Callbacks
irun -uvm ex4-21b_callbacks.sv -log irun_should_uvm_error_ex4_21b.log

#  Example 4-22: Simple Objection Mechanism
irun -uvm ex4-22_simple_objections.sv +UVM_OBJECTION_TRACE -log irun_should_uvm-error_ex4_22.log

#  Example 4-22: Objection Mechanism
irun -uvm ex4-22_objection_methods.sv +UVM_OBJECTION_TRACE -log irun_should_uvm_error_ex4_22a.log

#  Example 4-23: Heartbeat
irun -uvm ex4-23_heartbeat.sv -log irun_should_uvm_error_ex4_23.log

## Check Results
errors=0;
for file in `ls irun_ex4_*.log`
do
if (grep "*E," $file) then
  echo "--------------------------------------------------"
  echo " COMPILE/ELAB/SIM ERRORS - Check $file for details "
  echo "--------------------------------------------------"
  echo " TEST FAILED - Check $file file for details."
  let errors="errors+1"
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
echo " TOTAL ERRORS = $errors"
echo "--------------------------------------------------"
