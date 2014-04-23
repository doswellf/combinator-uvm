/*-------------------------------------------------------------------------
File name   : gpio_driver.sv
Title       : GPIO SystemVerilog UVM OVC
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


`ifndef GPIO_DRIVER_SV
`define GPIO_DRIVER_SV

class gpio_driver extends uvm_driver #(gpio_transfer);

  // The virtual interface used to drive and view HDL signals.
  virtual gpio_if gpio_if;

  // Provide implmentations of virtual methods such as get_type_name and create
  `uvm_component_utils(gpio_driver)

  // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

//UVM connect_phase
function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (!uvm_config_db#(virtual gpio_if)::get(this, "", "gpio_if", gpio_if))
   `uvm_error("NOVIF",{"virtual interface must be set for: ",get_full_name(),".gpio_if"})
endfunction : connect_phase

  // run phase
  virtual task run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
    join
  endtask : run_phase

  // get_and_drive 
  virtual protected task get_and_drive();
    uvm_sequence_item item;
    gpio_transfer this_trans;
    @(posedge gpio_if.n_p_reset);
    forever begin
      @(posedge gpio_if.pclk);
      seq_item_port.get_next_item(req);
      if (!$cast(this_trans, req))
        `uvm_fatal("CASTFL", "Failed to cast req to this_trans in get_and_drive")
      drive_transfer(this_trans);
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  // reset_signals
  virtual protected task reset_signals();
      @(negedge gpio_if.n_p_reset);
      gpio_if.gpio_pin_in  <= 'b0;
  endtask : reset_signals

  // drive_transfer
  virtual protected task drive_transfer (gpio_transfer trans);
    if (trans.delay > 0) begin
      repeat(trans.delay) @(posedge gpio_if.pclk);
    end
    drive_data(trans);
  endtask : drive_transfer

  virtual protected task drive_data (gpio_transfer trans);
    @gpio_if.pclk;
    for (int i = 0; i < `GPIO_DATA_WIDTH; i++) begin
      if (gpio_if.n_gpio_pin_oe[i] == 0) begin
        trans.transfer_data[i] = gpio_if.gpio_pin_out[i];
        gpio_if.gpio_pin_in[i] = gpio_if.gpio_pin_out[i];
      end else
        gpio_if.gpio_pin_in[i] = trans.transfer_data[i];
    end
    `uvm_info("GPIO_DRIVER", $sformatf("GPIO Transfer:\n%s", trans.sprint()), UVM_MEDIUM)
  endtask : drive_data

endclass : gpio_driver

`endif // GPIO_DRIVER_SV

