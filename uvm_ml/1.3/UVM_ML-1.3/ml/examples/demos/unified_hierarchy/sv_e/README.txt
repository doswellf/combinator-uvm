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

This demo shows how to construct a unified hierarchy by incorporating a UVM-e 
IP in a UVM-SV verification environment. The UVM-SV environment and the 
embedded UVM-e IP exchange TLM2 transactions.

The UVM-SV top component "svtop" has an env component with a producer and a 
consumer. In addition it has a UVM-e child component which is an env with a 
producer and consumer.

The UVM-SV top component configures the UVM-e and UVM-SV env components using
the configuration mechanism:
      set_config_int("*producer","address", ($urandom() & 'hffff));
      set_config_int("*env","e_active",e_active);
      set_config_int("*env","sv_active",sv_active);
Setting one of the IP "*_active" to FALSE results in the corresponding "env" 
component not instantiating the producer.

to set-up the environment refer to the README file at the top of this package. 

to run the demo on IES 12.2 and OSCI: 
	% demo.sh IES

to run with VCS 2011.12-2 and OSCI:
	% demo.sh VCS

to run with QUESTA 10.1d and OSCI:
	% demo.sh QUESTA


files:
README.txt - this file
demo.sh - shell script to invoke the demo
producer.e - e code for the initiator of transactions 
consumer.e - e code for the target for the transactions
env.e - e env code
top.e - e top level code
env.sv - SV IP environment code
producer.sv - SV definition of the initiator of transactions
consumer.sv - SV definition of the target for the transactions
svtop.sv - SV test code
Makefile - Makefile
Makefile.ies - makefile used for IES simulation
Makefile.vcs - makefile used for VCS simulation
Makefile.questa - makefile used for questa simulation
