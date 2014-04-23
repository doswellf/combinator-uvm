## 
## -------------------------------------------------------------
##    Copyright 2010 Cadence.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
## 
export
.PHONY: default ies ies_proc ies_ncsc_cl ies_ncsc_proc ies_osci ies_osci_proc vcs gui clean distclean questa questa_osci_proc
default ies ies_proc ies_ncsc_cl ies_ncsc_proc ies_ncsc_cl_multistep ies_ncsc_proc_multistep:
	$(MAKE) -f Makefile.ies $@
gui:
	$(MAKE) -f Makefile.ies ies_proc EXIT_OPT="" GUI_OPT="-gui"
ies_osci ies_osci_proc ies_osci_cl ies_osci_cl_multistep ies_osci_proc_multistep: 
	@/bin/true
vcs:
	$(MAKE) -f Makefile.vcs run
questa questa_osci_proc: 
	$(MAKE) -f Makefile.questa run
clean:
	$(MAKE) -f Makefile.ies $@
	$(MAKE) -f Makefile.vcs $@
	$(MAKE) -f Makefile.questa distclean

