/*-------------------------------------------------------------------------
File name   : test_lib.sv
Title       : Library of tests
Project     :
Created     :
Description : Library of tests for the APB-UART Environment
Notes       : Includes all the test files. Whenever a new test case file is 
            : created the file has to be included here
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

`include "uart_apb_incr_data.sv"
`include "apb_uart_rx_tx.sv"
`include "apb_to_uart_1stopbit.sv"
`include "uart_rx_tx_fifo_coverage.sv"
`include "u2a_incr_payload.sv"
`include "u2a_incr_payld_bd_parity.sv"
`include "error_reg_seq.sv"
