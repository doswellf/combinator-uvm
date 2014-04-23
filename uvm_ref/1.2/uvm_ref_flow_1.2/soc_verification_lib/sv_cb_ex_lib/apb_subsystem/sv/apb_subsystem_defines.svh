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


`ifndef APB_SUBSYSTEM_DEFINES_SVH
`define APB_SUBSYSTEM_DEFINES_SVH

`define AM_SPI0_BASE_ADDRESS    32'h800000      // SPI0 Base Address
`define AM_UART0_BASE_ADDRESS   32'h810000      // UART0 Base Address
`define AM_GPIO0_BASE_ADDRESS   32'h820000      // GPIO0 Base Address
`define AM_UART1_BASE_ADDRESS   32'h880000      // UART1 Base Address
`define AM_SPI0_END_ADDRESS    32'h80FFFF       // SPI0 END Address
`define AM_UART0_END_ADDRESS   32'h81FFFF       // UART0 END Address
`define AM_GPIO0_END_ADDRESS   32'h82FFFF       // GPIO0 END Address
`define AM_UART1_END_ADDRESS   32'h88FFFF       // UART1 END Address

`endif
