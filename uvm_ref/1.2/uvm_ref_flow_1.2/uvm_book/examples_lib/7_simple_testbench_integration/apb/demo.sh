#!/bin/sh

DEMO_HOME=`dirname $0`
TB_HOME=$DEMO_HOME/examples
TEST_NAME=test_read_after_write
#TEST_NAME=test_multiple_read_after_write
#TEST_NAME=test_seq_lib

export TB_HOME

usage() {
    echo "Usage:  demo.sh [-test <test_file>]"
    echo "                [-batch]"
    echo ""
    echo "                ... all other Incisive Simulator/UVM options such as:"
    echo "                [+UVM_VERBOSITY=UVM_NONE | UVM_LOW | UVM_MEDIUM | UVM_HIGH | UVM_FULL]"
    echo "                [+UVM_SEVERITY=INFO | WARNING | ERROR | FATAL]"
    echo "                [-SVSEED  random | <integer-value>]"
    echo ""
    echo "        demo.sh -h[elp]"
    echo ""
}

# =============================================================================
# Get args
# =============================================================================
gui="-access rc -linedebug -gui +tcl+$TB_HOME/sim_command.tcl"
other_args="";

while [ $# -gt 0 ]; do
   case $1 in
      -h|-help)
                        usage
                        exit 1
                        ;;
      -batch)
                        gui=""
                        ;;
      *)
                        other_args="$other_args $1"
                        ;;
    esac
    shift
done

# =============================================================================
# Execute
# =============================================================================

#  +uvm_set_verbosity=uvm_test_top.demo_tb0.apb0.slave*.collector,_ALL_,UVM_NONE,phase,run_phase \
#  +uvm_set_verbosity=uvm_test_top.demo_tb0.apb0.slave*.monitor,_ALL_,UVM_NONE,time,50 \
#  +uvm_set_verbosity=uvm_test_top.demo_tb0.apb0.slave*.collector,_ALL_,UVM_NONE,time,50 \
#  +uvm_set_verbosity=uvm_test_top.demo_tb0.apb0.master.monitor,_ALL_,UVM_NONE,time,50 \
#  +uvm_set_verbosity=uvm_test_top.demo_tb0.apb0.master.collector,_ALL_,UVM_NONE,time,50 \
#  +uvm_set_config_int=uvm_test_top.demo_tb0.apb0.master.monitor,coverage_enable,1 \
#irun -uvmhome $UVM_HOME \
irun -uvm \
  -incdir ./ \
  -incdir $DEMO_HOME/sv \
  -incdir $DEMO_HOME/examples \
  +UVM_VERBOSITY=UVM_HIGH \
  -coverage b:u \
  -covoverwrite \
  -nowarn PMBDVX \
  +UVM_TESTNAME=$TEST_NAME \
  -svseed random \
  $TB_HOME/demo_top.sv \
  +uvm_set_config_int=uvm_test_top.demo_tb0.apb0.*,coverage_enable,0 \
  +uvm_set_config_int=uvm_test_top.demo_tb0.apb0.bus_monitor,coverage_enable,1 \
  $gui \
  $other_args
