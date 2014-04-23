/*-------------------------------------------------------------------------
File name   : uart_ctrl_defines.svh
Title       : UART Controller defines
Project     :
Created     :
Description : defines for the UART Controller Environment
Notes       : 
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


`ifndef UART_CTRL_DEFINES_SVH
`define UART_CTRL_DEFINES_SVH

`define RX_FIFO_REG 32'h00
`define TX_FIFO_REG 32'h00
`define INTR_EN 32'h01
`define INTR_ID 32'h02
`define FIFO_CTRL 32'h02
`define LINE_CTRL 32'h03
`define MODM_CTRL 32'h04
`define LINE_STAS 32'h05
`define MODM_STAS 32'h06

`define DIVD_LATCH1 32'h00
`define DIVD_LATCH2 32'h01

`define UA_TX_FIFO_DEPTH 14

`endif
