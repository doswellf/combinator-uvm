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

test: 
	Pass transactions from SC producer to SV consumer and from SV producer 
	to SC consumer. Exercise all supported TLM1 ports. 

environment: 
	IES: Native IES SV working with NC SystemC + UVM-SC
	IES_OSCI: Native IES SV working with UVM-SC + Modified OSCI
	VCS: Native VCS SV working with UVM-SC + Modified OSCI
	QUESTA: Native QUESTA SV working with UVM-SC + Modified OSCI

to run: Make sure to source ml/setup.sh once before running any of the tests
	% make ies
        or
	% make ies_osci_proc
        or
        % make vcs
        or
        % make questa