/*-------------------------------------------------------------------------
File name   : uart_seq_lib.sv
Title       : sequence library file for uart uvc
Project     :
Created     :
Description : describes all UART UVC sequences
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

//-------------------------------------------------
// SEQUENCE: uart_base_seq
//-------------------------------------------------
class uart_base_seq extends uvm_sequence #(uart_frame);
  function new(string name="uart_base_seq");
    super.new(name);
  endfunction

  `uvm_object_utils(uart_base_seq)
  `uvm_declare_p_sequencer(uart_sequencer)

  // Use a base sequence to raise/drop objections if this is a default sequence
  virtual task pre_body();
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence '",
                                              get_full_name(), "'"});
  endtask

  virtual task post_body();
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence '",
                                             get_full_name(), "'"});
  endtask
endclass : uart_base_seq

//-------------------------------------------------
// SEQUENCE: uart_incr_payload_seq
//-------------------------------------------------
class uart_incr_payload_seq extends uart_base_seq;
    rand int unsigned cnt;
    rand bit [7:0] start_payload;

    function new(string name="uart_incr_payload_seq");
      super.new(name);
    endfunction

   // register sequence with a sequencer 
   `uvm_object_utils(uart_incr_payload_seq)
   `uvm_declare_p_sequencer(uart_sequencer)

    constraint count_ct { cnt > 0; cnt <= 10;}

    virtual task body();
      `uvm_info(get_type_name(), "UART sequencer executing sequence...", UVM_LOW)
      for (int i = 0; i < cnt; i++) begin
        `uvm_do_with(req, {req.payload == (start_payload +i*3)%256; })
      end
    endtask
endclass: uart_incr_payload_seq

//-------------------------------------------------
// SEQUENCE: uart_bad_parity_seq
//-------------------------------------------------
class uart_bad_parity_seq extends uart_base_seq;
    rand int unsigned cnt;
    rand bit [7:0] start_payload;

    function new(string name="uart_bad_parity_seq");
      super.new(name);
    endfunction
   // register sequence with a sequencer 
   `uvm_object_utils(uart_bad_parity_seq)
   `uvm_declare_p_sequencer(uart_sequencer)

    constraint count_ct {cnt <= 10;}

    virtual task body();
      `uvm_info(get_type_name(),  "UART sequencer executing sequence...", UVM_LOW)
      for (int i = 0; i < cnt; i++)
      begin
         // Create the frame
        `uvm_create(req)
         // Nullify the constrain on the parity
         req.default_parity_type.constraint_mode(0);
   
         // Now send the packed with parity constrained to BAD_PARITY
        `uvm_rand_send_with(req, { req.parity_type == BAD_PARITY;})
      end
    endtask
endclass: uart_bad_parity_seq

//-------------------------------------------------
// SEQUENCE: uart_transmit_seq
//-------------------------------------------------
class uart_transmit_seq extends uart_base_seq;

   rand int unsigned num_of_tx;
   // register sequence with a sequencer 
   `uvm_object_utils(uart_transmit_seq)
   `uvm_declare_p_sequencer(uart_sequencer)
   
   function new(string name="uart_transmit_seq");
      super.new(name);
   endfunction

   constraint num_of_tx_ct { num_of_tx <= 250; }

   virtual task body();
     `uvm_info(get_type_name(), $sformatf("UART sequencer: Executing %0d Frames", num_of_tx), UVM_LOW)
     for (int i = 0; i < num_of_tx; i++) begin
        `uvm_do(req)
     end
   endtask: body
endclass: uart_transmit_seq

//-------------------------------------------------
// SEQUENCE: uart_no_activity_seq
//-------------------------------------------------
class no_activity_seq extends uart_base_seq;
   // register sequence with a sequencer 
  `uvm_object_utils(no_activity_seq)
  `uvm_declare_p_sequencer(uart_sequencer)

  function new(string name="no_activity_seq");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info(get_type_name(), "UART sequencer executing sequence...", UVM_LOW)
  endtask
endclass : no_activity_seq

//-------------------------------------------------
// SEQUENCE: uart_short_transmit_seq
//-------------------------------------------------
class uart_short_transmit_seq extends uart_base_seq;

   rand int unsigned num_of_tx;
   // register sequence with a sequencer 
   `uvm_object_utils(uart_short_transmit_seq)
   `uvm_declare_p_sequencer(uart_sequencer)
   
   function new(string name="uart_short_transmit_seq");
      super.new(name);
   endfunction

   constraint num_of_tx_ct { num_of_tx inside {[2:10]}; }

   virtual task body();
     `uvm_info(get_type_name(), $sformatf("UART sequencer: Executing %0d Frames", num_of_tx), UVM_LOW)
     for (int i = 0; i < num_of_tx; i++) begin
        `uvm_do(req)
     end
   endtask: body
endclass: uart_short_transmit_seq
