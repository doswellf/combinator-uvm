//------------------------------------------------------------------------------
//
//            CADENCE                    Copyright (c) 2007
//                                       Cadence Design Systems, Inc.
//                                       All rights reserved.
//
// This work may not be copied, modified, re-published, uploaded, executed, or
// distributed in any way, in any medium, whether in whole or in part, without
// prior written permission from Cadence Design Systems, Inc.
//------------------------------------------------------------------------------
//
// Script Name   : rtl_clp.do 
// Usage         : This script is used to run the  CLP(Conformal Low Power) command. 
//                 This file sets the different options for low power.Read the  library and RTL files.
//                 After that CPF file is read and inserted.All the violations report are generated. 
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

// Set the log file name - rtl_clp.log
set log file $MY_WORK_AREA/rtl_clp.log  -replace

// lowpower option set the behaviour of low power checks. "-netlist_style" option indicates the design is
// physical netlist or logical netlist. For RTL level, logical netlist is used
set lowpower option -netlist_style logical
set lowpower option -ignore_high_to_low 0.2

// Use -isolation_check option to identify isolation errors.
set lowpower option -isolation_check advanced 

// Use the read library command to read the library file.
read library -statetable -liberty $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/power_ctrl/lib/sample.lib 

// Add the search path for the design files.
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/apb_subsystem/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/spi/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/gpio/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/uart/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/apic/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/smc/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/misc/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/mem_wrap/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/padframe/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/arm_subsystem/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/busmatrix/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/rom_subsystem/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/sram_subsystem/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/usb_subsystem/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/dma/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/macb/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/wb_to_ahb/rtl 
add search path $SPECMAN_HOME/sn_lib/osl/osp/hdl/oc_or1k/hdl

// Change RET2 for this design to Warning
set rule handling RET2 -Warning

// Used read design command to read the design file. Do not elaborate the design.
read design -verilog2k -file $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/socv/rtl/socv.filelist  -noelab -lastmod  
elaborate design
//report design data

// CPF file defines the low power intent of the design. Read cpf command is used to read the cpf file.
read cpf file $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/socv/cpf/socv_integ.cpf  -verbose  

// write the integrated cpf
write cpf socv_top.cpf -replace -integrated -expand_lib

// read this back
read cpf file $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/socv/cpf/socv_top.cpf  -verbose  

// After parsing the CPF file , low power insertion cell is done by commit cpf command.
commit cpf -insert 
//commit cpf  

analyze power domain



