/*-------------------------------------------------------------------------
File name   : apb_subsystem_vir_sequencer.sv
Title       : Virtual sequencer
Project     :
Created     :
Description : This file implements the Virtual sequencer for APB-UART environment
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

class apb_subsystem_virtual_sequencer extends uvm_sequencer;

    ahb_pkg::ahb_master_sequencer ahb_seqr;
    uart_pkg::uart_sequencer uart0_seqr;
    uart_pkg::uart_sequencer uart1_seqr;
    spi_sequencer spi0_seqr;
    gpio_sequencer gpio0_seqr;
    apb_ss_reg_model_c reg_model_ptr;
    
    function new (string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    `uvm_component_utils_begin(apb_subsystem_virtual_sequencer)
       `uvm_field_object(reg_model_ptr, UVM_DEFAULT | UVM_REFERENCE)
    `uvm_component_utils_end

endclass : apb_subsystem_virtual_sequencer

