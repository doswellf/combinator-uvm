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
// Script Name   : rtl_clp_wkshp.do 
// Usage         : This script is used to run the  CLP(Conformal Low Power) command.
//                 This file sets the different options for low power.Read the  library and RTL files.
//                 After that CPF file is read and inserted.All the violations report are generated.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

// Set  the log file name - rtl_clp.log
set log file $MY_WORK_AREA/conformal_lab/rtl_clp.log -replace  

// 1. lowpower option set the behaviour of low power checks. "-netlist_style" option indicates the design is
// physical netlist or logical netlist. For RTL level, logical netlist is used
set lowpower option -netlist_style logical

// 2.  Read the library files
read library -cpf $MY_WORK_AREA/conformal_lab/apb_subsystem.cpf -statetable -liberty 

// Add the search path for the design files.
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/apb_subsystem/rtl 
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/spi/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/gpio/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/uart/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/apic/rtl
add search path $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/smc/rtl

// Used read design command to read the design file. Do not elaborate the design.
read design -verilog -file $SOCV_KIT_HOME/designs/socv/rtl/rtl_lpw/apb_subsystem/rtl/apb_subs.filelist  -noelab -lastmod  
// Elaborate the design  and Report the design information.
elaborate design
report design data

// 3. CPF file defines the low power intent of the design. Read cpf command is used to read the cpf file.
read cpf file $MY_WORK_AREA/conformal_lab/apb_subsystem.cpf  -verbose  

// 4.  After parsing the CPF file , low power insertion cell is done by commit cpf command.
commit cpf -insert 
add rule waiver CPF_RET20 1
//commit cpf  

report power domain
report power mode

// 5. Analyze power domains, detects  
//  a) Logic without power domains
//  b) Primarty ports without primary power domains
//  c) Missing isolation and level shifters
//  d) Invalid isolatio cells or placement
analyze power domain

set rule handling RETRULE1.4 -Warning

report cpf logic -verbose



