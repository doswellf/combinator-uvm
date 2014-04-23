
# NC-Sim Command File
# TOOL:	ncsim(64)	12.20-s005
#
#
# You can restore this configuration with:
#
#      irun -f $UVM_ML_HOME/ml/tests/irun_uvm_ml.64.f -64bit -debug -g -uvmlinedebug ./test.sv ./top.e +UVM_NO_RELNOTES -nocopyright -access rw -uvmhome $UVM_ML_HOME/ml/frameworks/uvm/sv/uvm-1.1c -DSC_INCLUDE_DYNAMIC_PROCESSES -sysc -tlm2 -I$UVM_ML_HOME/ml/adapters/uvm_sc -I$UVM_ML_HOME/ml/adapters/uvm_sc/common -I$UVM_ML_HOME/ml/adapters/uvm_sc/ncsc ./sc.cpp -ml_uvm -top topmodule -sctlmrecord -scregisterproberecordall on -input restore.tcl +mpssession+SPECMAN29835 -input temp.tcl
#

set tcl_prompt1 {puts -nonewline "ncsim> "}
set tcl_prompt2 {puts -nonewline "> "}
set vlog_format %h
set vhdl_format %v
set real_precision 6
set display_unit auto
set time_unit module
set heap_garbage_size -200
set heap_garbage_time 0
set assert_report_level note
set assert_stop_level error
set autoscope yes
set assert_1164_warnings yes
set pack_assert_off {}
set severity_pack_assert_off {note warning}
set assert_output_stop_level failed
set tcl_debug_level 0
set relax_path_name 1
set vhdl_vcdmap XX01ZX01X
set intovf_severity_level ERROR
set probe_screen_format 0
set rangecnst_severity_level ERROR
set textio_severity_level ERROR
set vital_timing_checks_on 1
set vlog_code_show_force 0
set assert_count_attempts 1
set tcl_all64 false
set tcl_runerror_exit false
set assert_report_incompletes 1
set show_force 1
set force_reset_by_reinvoke 0
set tcl_relaxed_literal 0
set probe_exclude_patterns {}
alias . run
alias iprof profile
alias quit exit
database -open -shm -into ncsim.shm _ncsim.shm

simvision -input restore.tcl.svcf
