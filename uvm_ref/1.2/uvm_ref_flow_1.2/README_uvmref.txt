UVM Reference Flow - Ver 1.2
June 2013

****************************************************************************** 
Terms and Conditions For Use
****************************************************************************** 
Please refer to the README_terms_and_conditions.txt file located under
<INCISIV_install_area/kits/VerificationKit>/README_terms_and_conditions.txt

****************************************************************************** 
Product	Information
****************************************************************************** 
The UVM Reference Flow applies the Universal Verification Methodology (UVM) on
a realistic set of examples, which begin by showing aspects of the verification of
a block, a Universal Asynchronous Receiver Transmitter (UART).

It then shows how to verify a cluster design (a APB subsystem) into which the UART
gets integrated along with other design components (viz. SPI, GPIO, Power Controller,
Timers etc)

******************************************************************************
What's New
******************************************************************************

- For UVM sv reference flow

This release of the UVM Reference Flow is completely aligned with 
the Universal Verification Methodology UVM 1.1 (uvm-1.1) as released by Accellera.
It includes the book examples from the UVM Book:
A Practical Guide to Adopting the Universal Verification Methodology (UVM) 
Second Edition (Kathleen Meade and Sharon Rosenberg)


- For UVM e reference flow

This release also includes a UVM-e Reference Flow which applies the Universal Verification
Methodology in e (UVM-e developed by Cadence) to the same block and cluster level 
Verification of UART and APB subsystem.The sample verification environments (both block 
and cluster level) contain UVCs based on eRM as well as using UVM-e. Both eRM and UVM-e 
compatible UVC's can be nicely integrated together and can work seamlessly. 
Thus, it ensures that all exiting eRM compliant environments need not to be re-coded to 
work with an UVM compatible environment. Usage of UVM-e Scoreboard package is also 
included in this release.

******************************************************************************
UVM Reference Flow Design Overview
******************************************************************************

The UVM Reference Flow design is based on an Ethernet Switch System-on-Chip
(SoC). The SoC has the following key components
  1. An Open RISC Processor 
  2. Open Core Ethernet Media Access controller (MAC)
  3. AMBA AHB network interconnect
  4. Address Look up table (ALUT)
  5. Support and Control functions. For instance power management and peripherals
     like UART, SPI, GPO, timer etc
  6. On-chip Memories and memory controllers


  
******************************************************************************
Getting Started
******************************************************************************

------------------------------
For IES System Verilog users only
------------------------------

  The Makefile uses "-uvmhome" switch to compile the uvm_pkg released 
  by Accellera as uvm-1.1. You need UVM library i.e. uvm-1.1 to be able 
  to run the UVM reference flows. 

  Note: All the flows in this release have been validated on the above mentioned
        library release and Incisive Enterprise Simulator (IES 12.2)

 Once you have untarred and installed the UVM library, do the following

  Set the UVM_HOME environment variable to the UVM Library install area

  - In csh
    % setenv UVM_HOME <UVM Library install area>/uvm-1.1

  - In bash
    % UVM_HOME=<UVM Library install area>/uvm-1.1
    % export UVM_HOME


------------------------------
For Specman 'e' users only  
------------------------------
 
For Cadence customers, IES 12.2 is required to run the UVM e flow


UVM Reference Flow Setup:
-------------------------
  Once you have installed the UVM reference Flow, please do the following in a terminal

  Set the SOCV_KIT_HOME variable to the installation folder and source the
  env.[c]sh

  - In csh
    %> setenv SOCV_KIT_HOME <INCISIV_install_dir>/kits/VerificationKit
    %> source $SOCV_KIT_HOME/env.csh
    
  - In bash
    %> SOCV_KIT_HOME=<INCISIV_install_dir>/kits/VerificationKit
    %> export SOCV_KIT_HOME
    %> . $SOCV_KIT_HOME/env.sh



******************************************************************************
Running a Simulation using Incisive Enterprise Simulator (IES)
******************************************************************************
Module level simulation for UVM System Verilog flow : 

  % $SOCV_KIT_HOME/soc_verification_lib/sv_cb_ex_lib/uart_ctrl/demo.sh

Module level simulation for UVM e flow : 

  % $SOCV_KIT_HOME/soc_verification_lib/uvm_e_ex_lib/uart_ctrl/demo.csh

Cluster level simulation for UVM System Verilog flow : 

  % $SOCV_KIT_HOME/soc_verification_lib/sv_cb_ex_lib/apb_subsystem/demo.sh 

Cluster level simulation for UVM e flow : 

  % $SOCV_KIT_HOME/soc_verification_lib/uvm_e_ex_lib/apb_subsystem/demo.csh 

******************************************************************************
Documentation
******************************************************************************
Ethernet Switch SoC Design 
   $SOCV_KIT_HOME/doc/uvm_flow_topics/uvm_ref_flow_design/ethernet_switch.pdf

Open Core IP documentation
   uart16550 : $SOCV_KIT_HOME/doc/kit_topics/opencores/uart16550/UART_spec.pdf
   or1200    : $SOCV_KIT_HOME/doc/kit_topics/opencores/or1200/doc/openrisc1200_spec.pdf
               $SOCV_KIT_HOME/doc/kit_topics/opencores/or1200/doc/openrisc_arch.pdf
   spi       : $SOCV_KIT_HOME/doc/kit_topics/opencores/spi/spi.pdf
   ethmac    : $SOCV_KIT_HOME/doc/kit_topics/opencores/ethmac/eth_design_document.pdf
               $SOCV_KIT_HOME/doc/kit_topics/opencores/ethmac/eth_speci.pdf
               $SOCV_KIT_HOME/doc/kit_topics/opencores/ethmac/ethernet_datasheet_OC_head.pdf
               $SOCV_KIT_HOME/doc/kit_topics/opencores/ethmac/ethernet_product_brief_OC_head.pdf
  
User Guides

   For UVM sv Flow : 

   $SOCV_KIT_HOME/doc/uvm_flow_topics/uvm_sv/uvm_sv_ref_flow_ug.pdf

   For UVM e Flow : 

   $SOCV_KIT_HOME/doc/uvm_flow_topics/uvm_e/uvm_e_ref_flow_ug.pdf


******************************************************************************
Directory Structure
******************************************************************************

Design Hierarchy

  designs/socv/rtl/rtl_lpw
                    |
                    +-- ahb2apb        : AMBA AHB to AMBA APB bridge
                    |
                    +-- alut           : Address Lookup Table
                    |
                    +-- apb_subsystem  : AMBA APB Subsystem
                    |
                    +-- cdn_busmatrix  : AMBA AHB bus matrix
                    |
                    +-- dma            : Direct Memory access controller
                    |
                    +-- gpio           : General Purpose I/O
                    |
                    +-- opencores
                    |  |-- ethmac      : Ethernet MAC
                    |  |-- or1200      : Open RISC processor
                    |  |-- spi         : Serial Peripheral Interface
                    |  |-- uart16550   : Universal Asynchronous Receiver
                                         Transmitter
                    |
                    +-- padframe
                    |
                    +-- power_ctrl     : Power Control module
                    |
                    +-- rom_subsystem  : ROM Controller
                    |
                    +-- smc            : Memory Controller
                    |
                    +-- socv           : SoC Top level
                    |
                    +-- sram_subsystem : SRAM subsystem
                    |
                    +-- ttc            : Triple timer controller
                    |
                    +-- wb_to_ahb      : Wishbone to AHB bridge


Verification Environment:
  soc_verification_lib/sv_cb_ex_lib/
                    |
                    |
                    +-- interface_uvc_lib
                    |  +-- ahb
                    |  +-- apb
                    |  +-- spi
                    |  +-- gpio
                    |  +-- uart
                    |
                    +-- uart_ctrl
                    |  +-- examples
                    |  +-- sv
                           contains reusable design verif files:
                           monitor, scoreboard, env, virtual sequencer,etc
                    |  +-- tb/
                    |      +-- scripts/  run.sh, Makefiles, tcl commands, etc
                    |      +-- sv/  non-reusable code for this (testbench, top)
                    |      +-- tests/  library of tests for the design
                    |
                    +-- apb_subsystem
                    |  +-- examples
                    |  +-- sv
                           contains reusable design verif files:
                           monitor, scoreboard, env, virtual sequencer,etc
                    |  +-- tb/
                    |      +-- scripts/  run.sh, Makefiles, tcl commands, etc
                    |      +-- sv/  non-reusable code for this (testbench, top)
                    |      +-- tests/  library of tests for the design

  soc_verification_lib/uvm_e_ex_lib/
                    |
                    |
                    +-- interface_uvc_lib
                    |  +-- ahb
                    |  +-- apb
                    |  +-- spi
                    |  +-- gpio
                    |  +-- uart
                    |
                    +-- uart_ctrl
                    |  +-- e
                           contains reusable design verif files:
                           monitor, scoreboard, env, virtual sequence,etc
                    |  +-- sve/
                    |      +-- scripts/  run.sh, tcl commands, etc
                    |      +-- e/  non-reusable code for this (testbench, top)
                    |      +-- tests/  library of tests for the design
                    |      +-- testbench/ Verilog files for the testbench
                    |
                    +-- apb_subsystem
                    |  +-- e/
                           contains reusable design verif files:
                           monitor, scoreboard, env, virtual sequence,etc
                    |  +-- sve/
                    |      +-- scripts/  run.sh, tcl commands, etc
                    |      +-- e/  non-reusable code for this (testbench, top)
                    |      +-- tests/  library of tests for the design
                    |      +-- testbench/ Verilog files for the testbench



******************************************************************************
Release Version :1.1 
******************************************************************************

- UVM sv flow

  The UVM Reference UVM Reference Flow 1.1 release is tested with UVM 1.1
  Library (uvm-1.1) (from Accellera) and Incisive Enterprise Simulator (IES) 12.2. 
  It should be possible to run the UVM sv Reference Flow on any IEEE 1800 Compliant 
  Simulator which supports UVM. 

- UVM e flow

  The UVM e Reference Flow (UVM Reference Flow Version 1.1) is tested with 
  Incisive Enterprise Simulator (IES) 12.2. It should be possible to run the UVM e Reference 
  Flow on any IEEE 1647 Compliant simulator which supports UVM. 

  For more information about using the UVM Reference Flow please 
  contact uvm_ref@cadence.com.
