/*-------------------------------------------------------------------------
File name   : gpio_defines.svh
Title       : APB - GPIO defines
Project     :
Created     :
Description : defines for the APB-GPIO Environment
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

`ifndef APB_GPIO_DEFINES_SVH
`define APB_GPIO_DEFINES_SVH

`define GPIO_DATA_WIDTH         32
`define GPIO_BYPASS_MODE_REG    32'h00
`define GPIO_DIRECTION_MODE_REG 32'h04
`define GPIO_OUTPUT_ENABLE_REG  32'h08
`define GPIO_OUTPUT_VALUE_REG   32'h0C
`define GPIO_INPUT_VALUE_REG    32'h10
`define GPIO_INT_MASK_REG       32'h14
`define GPIO_INT_ENABLE_REG     32'h18
`define GPIO_INT_DISABLE_REG    32'h1C
`define GPIO_INT_STATUS_REG     32'h20
`define GPIO_INT_TYPE_REG       32'h24
`define GPIO_INT_VALUE_REG      32'h28
`define GPIO_INT_ON_ANY_REG     32'h2C

`endif
