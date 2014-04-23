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
.PHONY: default bundle32 bundle64 clean
default: bundle32 bundle64
bundle32: 
	$(MAKE) -f Makefile.ncsim BITS=32
bundle64: 
	$(MAKE) -f Makefile.ncsim BITS=64
clean:
	$(MAKE) -f Makefile.ncsim clean BITS=64
	$(MAKE) -f Makefile.ncsim clean BITS=32
