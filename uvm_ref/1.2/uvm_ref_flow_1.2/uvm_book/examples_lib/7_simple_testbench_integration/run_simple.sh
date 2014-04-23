#!/bin/sh

#  UART Controller Test without Virtual Sequence (NO DUT)
irun -f run.f tb/uart_ctrl_test.sv +UVM_TESTNAME=u2a_a2u_rand_test -log irun_ex7_test1.log

#  UART Controller Test with Virtual Sequence (NO DUT)
irun -f run.f tb/uart_ctrl_test.sv +UVM_TESTNAME=u2a_a2u_vseq_test -log irun_ex7_test2.log

