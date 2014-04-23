
----------------------------------------------------------------------
   (C) Copyright 2013 Cadence Design Systems, Incorporated
   (C) Copyright 2013 Advanced Micro Devices, Inc.
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

                                 UVM_ML Demo

This simple environment demonstrates the basic features of ML-UVM. Two 
independent environments, one in e and one in SystemVerilog are co-simulated, 
exchanging data using TLM1 and TLM2 transactions in both directions, both 
blocking and non-blocking.

Each environment has an "env" component. The env components have
producer and consumer components. The producer generates data and sends it 
through the various ports and sockets, while the consumer reacts to the data 
using both the blocking and non-blocking interfaces.

to set-up the environment refer to the README file at the top of this package. 

to run the demo on IES 12.2:
	% make ies
	% demo.sh IES

to run with VCS 2011.12-2 and OSCI:
	% demo.sh VCS

to run with Questa 10.1d and OSCI:
	% demo.sh QUESTA


files:
README - this file
demo.sh - shell script to invoke the demo
test.sv - SV code
top.e - e code
Makefile - Makefile using irun
Makefile.ies - makefile used for IES simulation
Makefile.vcs - makefile used for VCS simulation
Makefile.questa - makefile used for QUESTA simulation
