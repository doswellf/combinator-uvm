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

The Tests directory
===================
This directory contains tests that together comprise a regression 
test suite. You can run these tests to check if your UVM-ML 
environment is set up correctly. They can also serve as small code 
examples of using the UVM-ML features.

To run the regression, you can use the following top level scripts:
   - run_ies_tests.sh - run the regression using the IES simulator
   - run_vcs_tests.sh - run the regression using the VCS simulator
   - run_questa_tests.sh - run the regression using the Questa simulator
   - run_e_tests.sh - run tests using Specman e
Each test resides in a separate directory with a Makefile to build 
and run. You can use this Makefile to run each test alone.
