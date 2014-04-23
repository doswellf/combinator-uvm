/*-------------------------------------------------------------------------
File name   : uart_rx_monitor.sv
Title       : monitor file for uart uvc
Project     :
Created     :
Description : descirbes UART Monitor
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


`ifndef UART_RX_MONITOR_SV
`define UART_RX_MONITOR_SV

class uart_rx_monitor extends uart_monitor;

  `uvm_component_utils_begin(uart_rx_monitor)
    `uvm_field_object(cfg, UVM_DEFAULT | UVM_REFERENCE)
  `uvm_component_utils_end

  covergroup rx_traffic_cg;
    FRAME_DATA: coverpoint cur_frame.payload { 
        bins zero = {0};
        bins smaller = {[1:127]};
        bins larger = {[128:254]};
        bins max = {255};
      }
    FRAME_MSB_LSB: coverpoint msb_lsb_data { 
        bins zero = {0};
        bins one = {1};
        bins two = {2};
        bins three = {3};
      }
  endgroup

  covergroup rx_protocol_cg;
    PARITY_ERROR_GEN: coverpoint cur_frame.error_bits[1] {
        bins normal = { 0 };
        bins parity_error = { 1 };
      }
    FRAME_BREAK: coverpoint cur_frame.error_bits[2] {
        bins normal = { 0 };
        bins frame_break = { 1 };
      }
  endgroup

  function new (string name, uvm_component parent);
    super.new(name, parent);
    rx_traffic_cg = new();
    rx_traffic_cg.set_inst_name ("rx_traffic_cg");
    rx_protocol_cg = new();    
    rx_protocol_cg.set_inst_name ("rx_protocol_cg");
  endfunction: new

  // Additional class methods
  extern virtual function void perform_coverage();
  extern virtual task start_synchronizer(ref bit serial_d1, ref bit serial_b);
  extern virtual function void report_phase(uvm_phase phase);

endclass: uart_rx_monitor

task uart_rx_monitor::start_synchronizer(ref bit serial_d1, ref bit serial_b);
  super.start_synchronizer(serial_d1, serial_b);
  forever begin
    @(posedge vif.clock);
    if (!vif.reset) begin
      serial_d1 = 1;
      serial_b = 1;
    end else begin
      serial_d1 = serial_b;
      serial_b = vif.rxd;
    end
  end
endtask : start_synchronizer

function void uart_rx_monitor::perform_coverage();
  super.perform_coverage();
  rx_traffic_cg.sample();
  rx_protocol_cg.sample();
endfunction : perform_coverage

function void uart_rx_monitor::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("UART Frames Collected:%0d", num_frames), UVM_LOW)
endfunction : report_phase


`endif  // UART_RX_MONITOR_SV
