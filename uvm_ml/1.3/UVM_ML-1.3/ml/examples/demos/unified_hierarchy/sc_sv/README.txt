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

                       UVM_ML Unified Hierarchy Demo

This demo shows how to construct a unified hierarchy by incorporating a SystemC 
IP in a SystemVerilog verification environment. The SV environment and the 
embedded SC IP exchange TLM2 transactions.

The SV test has an env component with a producer and a consumer. In addition it
has a testbench component which instantiates an SC IP. The IP also has an env 
with a producer and consumer.


to set-up the environment refer to the README file at the top of this package. 

to run the demo on IES 12.2 and OSCI: 
	% demo.sh IES

to run with VCS 2011.12-2 and OSCI:
	% demo.sh VCS

to run with Questa 10.1d and OSCI:
	% demo.sh QUESTA


files:
README - this file
demo.sh - shell script to invoke the demo
producer.h - SC definition of the initiator of transactions 
consumer.h - SC definition of the target for the transactions
sctop.cpp - SC top level
producer.sv - SV definition of the initiator of transactions
consumer.sv - SV definition of the target for the transactions
test.sv - SV top level
Makefile - Makefile
Makefile.ies - makefile used for IES simulation
Makefile.vcs - makefile used for VCS simulation
Makefile.questa - makefile used for QUESTA simulation
