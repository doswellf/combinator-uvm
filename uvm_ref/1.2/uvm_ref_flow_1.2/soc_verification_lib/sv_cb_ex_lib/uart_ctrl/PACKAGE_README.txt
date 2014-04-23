----------------------------------------------------------------------
Copyright 1999-2010 Cadence Design Systems, Inc.
All Rights Reserved Worldwide

Licensed under the Apache License, Version 2.0 (the
"License"); you may not use this file except in
compliance with the License.  You may obtain a copy of
the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in
writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.  See
the License for the specific language governing
permissions and limitations under the License.
----------------------------------------------------------------------
* Title: UART block level Test bench
* Name: uart_ctrl
* Modified: March 2011
* Comments to: uvm_ref@cadence.com

* Description:

This package contains UART block level testbench implemented in UVM


The package contains the following directories:

sv/  : UVM SystemVerilog source code, containing register memory sequencesa
       coverage, module uvc , etc.

tb/       : Simulation verification environement  
  scripts/   : scripts to run the environment
  sv/        : UVM components (non-reusable)
             : top level testbench
  tests/     : different test cases

* Installation:

    Please refer the following file for Installation.

          $SOCV_KIT_HOME/README.txt

* Demo:

To run the demo: 
  
     issue the following command in a suitable simulation directory:
       % $SOCV_KIT_HOME/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/demo.sh

