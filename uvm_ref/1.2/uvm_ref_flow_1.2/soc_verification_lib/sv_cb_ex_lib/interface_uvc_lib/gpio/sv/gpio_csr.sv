/*-------------------------------------------------------------------------
File name   : gpio_csr.sv
Title       : GPIO SystemVerilog UVM UVC
Project     : SystemVerilog UVM Cluster Level Verification
Created     :
Description : 
Notes       :  
---------------------------------------------------------------------------*/
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


`ifndef GPIO_CSR_SV
`define GPIO_CSR_SV

typedef struct packed {
  bit [`GPIO_DATA_WIDTH-1:0] bypass_mode;
  bit [`GPIO_DATA_WIDTH-1:0] direction_mode;
  bit [`GPIO_DATA_WIDTH-1:0] output_enable;
  bit [`GPIO_DATA_WIDTH-1:0] output_value;
  bit [`GPIO_DATA_WIDTH-1:0] input_value;
  bit [`GPIO_DATA_WIDTH-1:0] int_mask;
  bit [`GPIO_DATA_WIDTH-1:0] int_enable;
  bit [`GPIO_DATA_WIDTH-1:0] int_disable;
  bit [`GPIO_DATA_WIDTH-1:0] int_status;
  bit [`GPIO_DATA_WIDTH-1:0] int_type;
  bit [`GPIO_DATA_WIDTH-1:0] int_value;
  bit [`GPIO_DATA_WIDTH-1:0] int_on_any;
  } gpio_csr_s;

class gpio_csr extends uvm_object;

  //instance of CSRs
  gpio_csr_s csr_s;

  //randomize GPIO CSR fields
  rand bit [`GPIO_DATA_WIDTH-1:0] bypass_mode;
  rand bit [`GPIO_DATA_WIDTH-1:0] direction_mode;
  rand bit [`GPIO_DATA_WIDTH-1:0] output_enable;
  rand bit [`GPIO_DATA_WIDTH-1:0] output_value;
  rand bit [`GPIO_DATA_WIDTH-1:0] input_value;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_mask;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_enable;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_disable;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_status;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_type;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_value;
  rand bit [`GPIO_DATA_WIDTH-1:0] int_on_any;

  // this is a default constraint that could be overriden
  // Constrain randomisation of configuration based on UVC/RTL capabilities
  constraint c_default_config { int_mask         == 32'hFFFFFFFF;}

  // These declarations implement the create() and get_type_name() as well as enable automation of the
  // transfer fields   
  `uvm_object_utils_begin(gpio_csr)
    `uvm_field_int(bypass_mode,    UVM_ALL_ON)
    `uvm_field_int(direction_mode, UVM_ALL_ON)
    `uvm_field_int(output_enable,  UVM_ALL_ON)
    `uvm_field_int(output_value,   UVM_ALL_ON)
    `uvm_field_int(input_value,    UVM_ALL_ON)  
    `uvm_field_int(int_mask,       UVM_ALL_ON)
    `uvm_field_int(int_enable,     UVM_ALL_ON)
    `uvm_field_int(int_disable,    UVM_ALL_ON)
    `uvm_field_int(int_status,     UVM_ALL_ON)
    `uvm_field_int(int_type,       UVM_ALL_ON)
    `uvm_field_int(int_value,      UVM_ALL_ON)
    `uvm_field_int(int_on_any,     UVM_ALL_ON)
  `uvm_object_utils_end

  // This requires for registration of the ptp_tx_frame   
  function new(string name = "gpio_csr");
	  super.new(name);
  endfunction 
   
  function void post_randomize();
    Copycfg_struct();
  endfunction 

  function void Copycfg_struct();
    csr_s.bypass_mode    = bypass_mode;
    csr_s.direction_mode = direction_mode;
    csr_s.output_enable  = output_enable;
    csr_s.output_value   = output_value;
    csr_s.input_value    = input_value;
    csr_s.int_mask       = int_mask;
    csr_s.int_enable     = int_enable;
    csr_s.int_disable    = int_disable;
    csr_s.int_status     = int_status;
    csr_s.int_type       = int_type;
    csr_s.int_value      = int_value;
    csr_s.int_on_any     = int_on_any;
  endfunction

endclass : gpio_csr

`endif

