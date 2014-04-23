# ----------------------------------------------------------------------
#    Copyright 2012 Cadence Design Systems, Inc.
#    All Rights Reserved Worldwide
# 
#    Licensed under the Apache License, Version 2.0 (the
#    "License"); you may not use this file except in
#    compliance with the License.  You may obtain a copy of
#    the License at
# 
#        http://www.apache.org/licenses/LICENSE-2.0
# 
#    Unless required by applicable law or agreed to in
#    writing, software distributed under the License is
#    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
#    CONDITIONS OF ANY KIND, either express or implied.  See
#    the License for the specific language governing
#    permissions and limitations under the License.
# ----------------------------------------------------------------------
ARCH = lnx86

DEBUG_FLAGS = -g

.PHONY: default nodebug debug nodebug32 debug32 clean
 
default : nodebug

nodebug:
	$(MAKE) -f Makefile.osci ARCH=$(ARCH) BITS=64

debug:
	$(MAKE) -f Makefile.osci ARCH=$(ARCH) DEBUG_FLAGS=$(DEBUG_FLAGS) BITS=64

nodebug32:
	$(MAKE) -f Makefile.osci ARCH=$(ARCH) BITS=32

debug32:
	$(MAKE) -f Makefile.osci ARCH=$(ARCH) DEBUG_FLAGS=$(DEBUG_FLAGS) BITS=32

clean:
	$(MAKE) -f Makefile.osci ARCH=$(ARCH) clean BITS=64
	$(MAKE) -f Makefile.osci ARCH=$(ARCH) clean BITS=32

