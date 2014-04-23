#!/bin/sh

if [ "${UVM_SETUP_SAVE}" != "" ]; then
  if [ "${UVM_REF_HOME}" != "" ]; then
    if [ "${UVM_SETUP_SAVE}" = "${UVM_REF_HOME}" ]; then
        echo "UVM reference flow setup already done"
        exit 1
    else
        echo "Warning: Changing UVM_REF_HOME from "
        echo "         $UVM_SETUP_SAVE "
        echo "         to "
        echo "         $UVM_REF_HOME "
    fi
  fi
fi

if [ "${UVM_REF_HOME}" =  "" ]; then
  echo "************************************************************************************"
  echo "Error: UVM_REF_HOME environment variable not defined to <UVM ref flow install_dir>      "
  echo "Usage example:                                                                      "
  echo "  UVM_REF_HOME=/cad/install/uvm_ref_flow                                           "
  echo "  export UVM_REF_HOME                                                              "
  echo "  .  "\$"UVM_REF_HOME/env.sh                                                       "
  echo "************************************************************************************"
  exit
else
  if [ "${UVM_SETUP_SAVE}" = "" ]; then
    echo "UVM_REF_HOME set to $UVM_REF_HOME"
    if [ "${SPECMAN_PATH}" = "" ]; then
       SPECMAN_PATH=${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib
       export SPECMAN_PATH
    else 
       SPECMAN_PATH=${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib:${SPECMAN_PATH}
       export SPECMAN_PATH
    fi
    SPECMAN_PATH=${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib/apb_subsystem:${SPECMAN_PATH}
    export SPECMAN_PATH

    SPECMAN_PATH=${UVM_REF_HOME}/soc_verification_lib/uvm_e_ex_lib/interface_uvc_lib:${SPECMAN_PATH}
    export SPECMAN_PATH
  fi
fi

if [ "${UVM_HOME}" = "" ]; then
  echo "**********************************************************"
  echo "Warning: For UVM System Verilog users only :              " 
  echo "         UVM_HOME environment variable not defined    "
  echo "         Please set this to your UVM library install area "
  echo "         Please refer $UVM_REF_HOME/README.txt for Installation "
  echo "**********************************************************"
fi

UVM_SETUP_SAVE=${UVM_REF_HOME}
export UVM_SETUP_SAVE
  

