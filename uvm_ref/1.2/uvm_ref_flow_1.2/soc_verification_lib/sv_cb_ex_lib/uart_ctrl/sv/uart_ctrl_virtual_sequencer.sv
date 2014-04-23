/*-------------------------------------------------------------------------
File name   : uart_ctrl_virtual_sequencer.sv
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


class uart_ctrl_virtual_sequencer extends uvm_sequencer;

    apb_pkg::apb_master_sequencer apb_seqr;
    uart_pkg::uart_sequencer uart_seqr;
    //uart_ctrl_reg_sequencer reg_seqr;   //KAM - remove

    // UVM_REG: Pointer to the register model
    //uart_ctrl_reg_model_c reg_model;  //KAM - remove
   
    // Uart Controller configuration object
    uart_ctrl_config cfg;

    function new (input string name="uart_ctrl_virtual_sequencer", input uvm_component parent=null);
      super.new(name, parent);
    endfunction : new

    `uvm_component_utils_begin(uart_ctrl_virtual_sequencer)
       `uvm_field_object(cfg, UVM_DEFAULT | UVM_REFERENCE)
       //`uvm_field_object(reg_model, UVM_DEFAULT | UVM_REFERENCE)  //KAM - remove
    `uvm_component_utils_end

endclass : uart_ctrl_virtual_sequencer
