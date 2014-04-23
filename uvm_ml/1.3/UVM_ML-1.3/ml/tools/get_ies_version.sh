#!/bin/csh -f 
set full_ies_version="UNKNOWN"
set NCROOT_PATH=`/usr/bin/which ncroot`
if ( ( ${%NCROOT_PATH} != 0 ) ) then
    set full_ies_version = `irun -version`
else
    set SN_EXEC_PATH=`/usr/bin/which specman`
    if ( ( ${%SN_EXEC_PATH} != 0 ) ) then
        set full_ies_version = `specman -version`
    endif
endif

if ( "$full_ies_version" =~ {*12.2*} ) then
    echo 12.2
else if ( "$full_ies_version" =~ {*13.1*} ) then
    echo 13.1
else if ( "$full_ies_version" =~ {*13.2*} ) then
    echo 13.2
else # By default
    echo 12.2
endif

