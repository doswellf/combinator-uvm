/*-------------------------------------------------------------------------
File name   : apb_uart_rx_tx_data_aa.sv
Title       : Test Case
Project     :
Created     :
Description : One test case for the APB-UART Environment
Notes       : The test creates a apb_uart_sve and sets the default
            : sequence for the sequencer as concurrent_u2a_a2u_rand_trans
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


class uart_frame_aa extends uart_pkg::uart_frame;
  `uvm_object_utils(uart_frame_aa)  
  constraint payload_ct  { payload == 8'haa; }
endclass : uart_frame_aa

class apb_uart_rx_tx_data_aa extends apb_uart_rx_tx;

  `uvm_component_utils(apb_uart_rx_tx_data_aa)

  function new(input string name, 
                input uvm_component parent=null);
      super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    set_type_override_by_type(uart_pkg::uart_frame::get_type(), uart_frame_aa::get_type());
    super.build_phase(phase);
  endfunction : build_phase

endclass
