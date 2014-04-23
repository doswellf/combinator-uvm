#!/bin/sh -f


irun -c -mess \
 -f ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/socv/topologies/or1k.topology \
 -F ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/socv/rtl/socv.irunargs \
 -F ${SOCV_KIT_HOME}/designs/socv/rtl/rtl_lpw/socv/rtl/socv_or1k.irunargs

