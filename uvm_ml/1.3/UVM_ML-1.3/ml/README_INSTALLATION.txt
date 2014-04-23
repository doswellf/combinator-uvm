

UVM-ML: the UVM Multi Language Verification Methodology Package

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

This package contains the UVM-ML solution code, along with
documentation and examples to demonstrate typical use cases.

Following is a short explanation how to install the package and run 
a first basic example to verify that the installation is operational. 

If you have any issues, consult the trouble shooting section in the 
QuickStart.pdf.

For more information about the package please open ml/README.html. 
It gives a hyperlinked list of all relevant material and suggests 
where to start reading from.

Tools
-----
To build the library and run the examples, you need the tools listed below.
A subset of these tools may be sufficient, depending on the simulators and 
programming languages you use. You should use the same versions of the tools 
as specified below. Other versions were not verified; therefore they might not 
work or might work only partially.

The suggested tools and versions are:
1. For simulation use one or more of:
   o Cadence IES: version 12.20-s012 or later - native support for 
     SV, e and SC
   o Synopsys VCS: version 2011.12.2 or 2013.9-SP1 - SV simulation requires 
     external e/SC
   o Mentor Questa: version 10.1d - SV simulation requires external e/SC
   o OSCI SystemC version systemc-2.2.0 or 2.3.0 - SC simulation with any of 
     the simulators above (available on
     http://www.accellera.org/downloads/standards/systemc)
   o Specman e: version 12.20.006-s or later - e simulation with VCS or Questa


2. Language libraries
   o TLM version - TLM 2.0.1 (2009-07-15) only for SystemC 2.2 because version 
     2.3 already includes TLM (available on  
     http://www.accellera.org/downloads/standards/systemc)
   o UVM-SV ML-enabled version - already included in this package (uvm-1.1c 
     included in this package is an ML-enabled version of UVM-SV)

3. To build the package use:
   o GCC version - v4.4.5
   o GNU Make 3.81

Notes: 
   o The package was designed to work with different simulators, on Linux 
     operating system only. So far, it was tested with IES, VCS, Questa and 
     OSCI SystemC. 
   o We recommend using either IES or VCS or Questa. Installing multiple tools 
     in the same environment may lead to unexpected conflicts.


Quick installation
------------------
To install the package simply untar it in some clean directory.
Then change directory into the top level directory UVM_ML-xxx (where xxx is 
the version number of this release). The default installation from the 
directory where the tar file was opened is as follows:

For IES users:
   % set path=( <path to irun> $path)
   % source ml/setup_ies.sh

For VCS users (see below instructions for installing TLM2 and OSCI SystemC):
     Set VCS_HOME to point to the installation of the simulator.
   % set path=( <path to vcs> $path)
   % setenv OSCI_VERSION 2.<x>
	e.g. 2.2 or 2.3
   % setenv OSCI_INSTALL <path to osci 2.x compiled with g++-4.4.5-pic>
      this is the same directory provided as --prefix to OSCI's configuration
      e.g. .../2.2/g++-4.4.5-pic
   % setenv OSCI_SRC <path to source for OSCI SystemC>
      e.g. .../systemc/systemc-2.2.0
   % setenv TLM2_INSTALL <path to installation of SystemC TLM-2009-07-15>
      e.g. .../TLM-2009-07-15            // for SC version 2.2
      e.g. setenv TLM2_INSTALL $OSCI_SRC // for SC version 2.3
   % source ml/setup_vcs.sh

For Questa users (see below instructions for installing TLM2 and OSCI SystemC):
     Set MTI_HOME to point to the installation of the simulator.
   % set path=( <path to questa> $path)
   % setenv OSCI_VERSION 2.<x>
	e.g. 2.2 or 2.3
   % setenv OSCI_INSTALL <path to osci 2.x compiled with g++-4.4.5-pic>
      this is the same directory provided as --prefix to OSCI's configuration
      e.g. .../2.2/g++-4.4.5-pic
   % setenv OSCI_SRC <path to source for OSCI SystemC>
      e.g. .../systemc/systemc-2.2.0
   % setenv TLM2_INSTALL <path to installation of SystemC TLM-2009-07-15>
      e.g. .../TLM-2009-07-15            // for SC version 2.2
      e.g. setenv TLM2_INSTALL $OSCI_SRC // for SC version 2.3
   % source ml/setup_questa.sh

Note: Various options are provided to control the setup_*.sh script:
      To setup the environment for a 32 bit machine use --32bit
      To build without the OSCI option (for IES only) use --no-osci
      To build without Specman (SV/SC only) use --no-specman
      To avoid rebuilding the backplane use --no-backplane
      To avoid rebuilding BOOST use --no-boost
      To rebuild the entire package use --clean
      To set up the environment without rebuilding use --env_only

The setup.sh script generates two files listing the environment variable 
setting in $(UVM_ML_HOME)/ml:
 - setup.captured.sh (CSH format) 
 - setup.captured.mk (make format) 
When you start working in a new environment, source setup.captured.sh to set up 
the environment.

If you need non standard setup see the sections below explaining the
various options to install and configure UVM-ML


Running an Example
------------------
Run a simple demo to make sure your installation was successful:

   % cd $UVM_ML_HOME/ml/examples/demos/prod_cons/sc_sv
   % demo.sh <IES|VCS|QUESTA>
Or use the Makefile to run in GUI mode e.g.
   % make ies GUI_OPT="-gui" EXIT_OPT=""

- More demo examples can be found in $UVM_ML_HOME/ml/examples/demos. 
  A README file in each demo directory explains how to run the 
  demo in various environments. 

- Additional small examples are available under the
  $UVM_ML_HOME/ml/tests directory. There you can find makefiles to run each 
  of the tests.

Note: A more detailed explanation on running the examples can be found 
in the Quick Start document (location in the installed package: 
$UVM_ML_HOME/ml/docs/QuickStart.pdf).


Installing OSCI SystemC and TLM2
--------------------------------
TLM2 and the OSCI SystemC simulator can be downloaded from 
http://www.accellera.org/downloads/standards/systemc. You can select 
systemc-2.3.0.tgz that includes TLM, or systemc-2.2.0.tgz and TLM-2.0.1.tgz.

Installation of TLM is simply opening the tar and setting the appropriate 
environment variable as shown above.

Instructions how to install the OSCI SystemC simulator can be found in 
http://openesl.org/systemc-wiki/Installation. Note however that the use model 
of UVM-ML requires compiling the OSCI engine into a shared library. To get 
a position independent 64-bit shared library one must pass the "-fPIC" flag 
to g++. 

So to compile the 64-bit OSCI library fit for UVM-ML usage, please build it as 
follows: 
   % gmake CFLAGS='-fPIC' CXXFLAGS='-fPIC' LDFLAGS='-fPIC' \
     EXTRA_CXXFLAGS='-fPIC' install
   % gmake check
Then set the appropriate environment variable to the directory you provided 
in the --prefix flag in the configuration script

Note: UVM-ML was tested using g++ 4.4.5. Please compile the OSCI engine using 
the same compiler.


Re-building the package manually
--------------------------------
If there is need to incorporate UVM_ML_OA in a proprietary flow instead of 
using the setup.sh, one must be aware of proper usage of specfiles.
 - UVM-ML-OA 1.3 includes its own specfiles in $UVM_ML_HOME/ml/tools/specfiles,
   and further on per IES version. Each subdirectory contains specfiles for g++
   4.4 and 4.1; the names should be self-explanatory.
 - Our Makefiles use the UVM_ML_COMPILER_VERSION environment variable to refer 
   to the appropriate specfile. If undefined, the variable is deduced 
   automatically by running $UVM_ML_CC -version and analyzing its output. In 
   general, "-gcc_vers <desired version> -spec <desired specfile>" should be 
   passed to irun/ncsc_run.
 - The specfiles in question are MANDATORY for IES users. Failing to state the 
   appropriate specfile may cause IES-supplied UVM-SC headers to be used 
   instead of UVM-ML ones, resulting in all kinds of compilation and simulation
   failures hard to decipher


