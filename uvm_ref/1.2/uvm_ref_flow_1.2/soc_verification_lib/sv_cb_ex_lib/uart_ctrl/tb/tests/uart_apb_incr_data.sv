/*-------------------------------------------------------------------------
File name   : uart_apb_incr_data.sv
Title       : Test Case
Project     :
Created     :
Description : One test case for the APB-UART Environment
Notes       : The test creates a uart_ctrl_tb and sets the default
            : sequence for the sequencer as u2a_incr_payload_vseq
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

class uart_apb_incr_data extends uvm_test;

  uart_ctrl_tb uart_ctrl_tb0;

  `uvm_component_utils(uart_apb_incr_data)

  function new(input string name, 
                input uvm_component parent=null);
      super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    uvm_config_db#(uvm_object_wrapper)::set(this, "uart_ctrl_tb0.virtual_sequencer.run_phase",
          "default_sequence", u2a_incr_payload_vseq::type_id::get());
    uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0",this);
  endfunction : build_phase

endclass
