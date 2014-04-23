/*-------------------------------------------------------------------------
File name   : uart_internal_if.sv
Title       : Interface File
Project     : UART Block Level
Created     :
Description : Interface for collecting white box coverage
Notes       :
----------------------------------------------------------------------
Copyright 2007 (c) Cadence Design Systems, Inc. All Rights Reserved.
----------------------------------------------------------------------*/

interface uart_ctrl_internal_if(input clock);
 
  int tx_fifo_ptr ;
  int rx_fifo_ptr ;

endinterface  
