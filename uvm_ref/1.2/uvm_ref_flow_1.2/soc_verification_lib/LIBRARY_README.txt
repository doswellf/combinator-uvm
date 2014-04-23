Incisive Verification Kits
Version 09.20-s023, August 2010
Copyright (c) 2007 Cadence Design Systems, Inc. All rights reserved worldwide.
Please refer to the terms and conditions in 
******************************************************************************
* Title: The Soc Verification Kit library
* Version: 09.20-s023 
* Modified: August 2010
* Description:
 

   abv_formal  
          The Formal verification environment. Uses IFV 

   e_ex_lib
        |
        |-- cdn_apb_subsystem
        |       APB subsystem verification environment. Contains Testbench to do 
        |       a) Low power verification
        |       b) AMBA AHB compliance testing
        |       c) Reuse of block level UART "eRM" testbench 
        |
        |-- cdn_hw_sw: (only in soc verifiation kit)
        |      Software UVC
        |
        |-- cdn_uart_apb: Block level UART testbench implemented in eRM
        |
        |-- cdn_socv (only in soc verification kit)
        |            Contains the chip/system level verification environment capable of
        |            a) H/W-SW co-verification using ISX/GSA
        |            c) System level Low power testing 
        |
        |-- cdn_vm_ext:
        |           Incisive Manager extention files
        |
        |-- interface_uvc_lib:
        |         Contains Interface UVC's in eRM
        |
        |-- ivb_lib:
        |    IVB generated package for AHB Lite interface
        |
        |-- vr_scbd: Scoreboard utility
        |
   sv_cb_ex_lib
        |
        |-- apb_subsystem: Cluster level testbench implemented in the following
        |             verifiation languages:
        |            a) UVM Systemverilog
        |-- uart_ctrl: Block level UART testbench implemented in the following
        |             verifiation languages:
        |            a) UVM Systemverilog
        |-- interface_uvc_lib:
        |         Contains Interface UVC's in UVM SystemVerilog  
   sc_ex_lib
        |
        |-- ref_models: SC ref models
               |
               |-- cdn_uart_apb_tlm : SC reference model for the UART DUT
        |
   mixed_ex_lib
        |
        |-- sc_tlm_verification_lib: Mixed language environment using
                                     UVM-SV testbench with a SC reference model
        |
        |-- sv_class_over_e_lib: UVM-SV over e tetbench

* Installation:

    For csh users:
    1) Set environment variable SOCV_KIT_HOME to point to the root directory 
       of the SoC Kit installation. 


           % setenv SOCV_KIT_HOME <path_to_kit_installation>


    2) Execute the environment setup script


           % source $SOCV_KIT_HOME/env.csh 

         

    For sh/bash users:
    1) Set environment variable SOCV_KIT_HOME to point to the root directory 
       of the SoC Kit installation. 


           % SOCV_KIT_HOME=<path_to_kit_installation>
           % export SOCV_KIT_HOME;


    2) Execute the environment setup script


           % . $SOCV_KIT_HOME/env.sh 

         

