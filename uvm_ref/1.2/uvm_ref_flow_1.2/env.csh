#!/bin/csh -f

if ($?UVM_SETUP_SAVE != 0) then
  if ($?UVM_REF_HOME != 0) then
    if ($UVM_SETUP_SAVE == $UVM_REF_HOME) then
        echo "UVM reference flow setup already done"
        exit 1
    else # New install path
        echo "Warning: Changing UVM_REF_HOME from "
        echo "         $UVM_SETUP_SAVE "
        echo "         to "
        echo "         $UVM_REF_HOME "
    endif
  endif
endif

if ($?UVM_REF_HOME == 0) then
  echo "************************************************************************************"
  echo "Error: UVM_REF_HOME environment variable not defined to <UVM ref flow install_dir>      "
  echo "Usage example:                                                                      "
  echo "  setenv UVM_REF_HOME /cad/install/KITSOCV/libraries                               "
  echo "  source "\$"UVM_REF_HOME/env.csh                                                   "
  echo "************************************************************************************"
  exit
else
  if ($?UVM_SETUP_SAVE == 0) then
    echo "UVM_REF_HOME set to $UVM_REF_HOME"
    if ( $?SPECMAN_PATH == 0 ) then
      setenv SPECMAN_PATH ${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib
    else 
      setenv SPECMAN_PATH ${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib:${SPECMAN_PATH}
    endif
    setenv SPECMAN_PATH ${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib/apb_subsystem:${SPECMAN_PATH}
    setenv SPECMAN_PATH ${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib/interface_uvc_lib:${SPECMAN_PATH}
  endif
endif

if ($?UVM_HOME == 0) then
  echo "**********************************************************"
  echo "Warning: For UVM System Verilog users only : " 
  echo "         UVM_HOME environment variable not defined    "
  echo "         Please set this to your UVM library install area "
  echo "         Please refer $UVM_REF_HOME/README.txt for Installation "
  echo "**********************************************************"
endif


setenv UVM_SETUP_SAVE ${UVM_REF_HOME}

