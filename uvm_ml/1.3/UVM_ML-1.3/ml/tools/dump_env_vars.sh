#!/bin/csh -f 
##########################################################
#
# CSH format
# 
##########################################################



set dump_file=$UVM_ML_HOME/ml/setup.captured.sh
\rm -f $dump_file

echo '# UVM_ML setup capture' > $dump_file
echo '# Performed at' `date` >> $dump_file
echo >> $dump_file

set var_list="UVM_ML_CXX_OPTS UVM_ML_HOME OSCI_INSTALL OSCI_SRC TLM2_INSTALL UVM_ML_CC UVM_ML_LD UVM_ML_SVDPI_DIR UVM_ML_COMPILER_VERSION UVM_ML_OVERRIDE UNILANG_OVERRIDE IES_VERSION OSCI_VERSION"


foreach env_var ( $var_list )
if ( `eval echo \$\?$env_var` ) then
    set value=`eval echo \${${env_var}}`

    echo 'if ( \! ' \$\?$env_var ' ) then ' >> $dump_file
    echo "setenv  $env_var '$value' " >> $dump_file
    echo 'endif' >> $dump_file
    echo >>  $dump_file

endif
end

####################################################################
# 
# Makefile format
#
####################################################################

#	OSCI_INSTALL (if relevant)
#	OSCI_SRC (if relevant)
#	UVM_ML_CC
#	UVM_ML_LD
#	UVM_ML_COMPILER_VERSION (4.1, 4.4 etc)
#	UVM_ML_OVERRIDE
#	UNILANG_OVERRIDE
#	IES_VERSION (if relevant)
#	OSCI_VERSION (if relevant)

set dump_file=$UVM_ML_HOME/ml/setup.captured.mk

\rm -f $dump_file

echo '# UVM_ML setup capture' > $dump_file
echo '# Performed at' `date` >> $dump_file
echo >> $dump_file

foreach env_var ($var_list )
if ( `eval echo \$\?$env_var` ) then
    set value=`eval echo \${${env_var}}`
    echo "ifndef $env_var" >> $dump_file
    echo "$env_var := " $value >> $dump_file
    echo "export $env_var" >> $dump_file
    echo 'endif' >> $dump_file
    echo >>  $dump_file
endif
end
