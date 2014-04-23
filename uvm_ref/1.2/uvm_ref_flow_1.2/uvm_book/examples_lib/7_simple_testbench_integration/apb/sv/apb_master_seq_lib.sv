/*******************************************************************************
  FILE : apb_master_seq_lib.sv
*******************************************************************************/
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


`ifndef APB_MASTER_SEQ_LIB_SV
`define APB_MASTER_SEQ_LIB_SV

//------------------------------------------------------------------------------
// SEQUENCE: apb_master_base_seq  - active APB sequences should derive from this
//------------------------------------------------------------------------------
class apb_master_base_seq extends uvm_sequence #(apb_transfer);

  function new(string name="apb_master_base_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(apb_master_base_seq)
  `uvm_declare_p_sequencer(apb_master_sequencer)

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
endclass : apb_master_base_seq

//------------------------------------------------------------------------------
// SEQUENCE: read_byte_seq
//------------------------------------------------------------------------------
class read_byte_seq extends apb_master_base_seq;
  rand bit [31:0] start_addr;
  rand int unsigned transmit_del;

  function new(string name="read_byte_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(read_byte_seq)

  constraint transmit_del_ct { (transmit_del <= 10); }
    
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    `uvm_do_with(req, 
      { req.addr == start_addr;
        req.direction == APB_READ;
        req.transmit_delay == transmit_del; } ) 
    //get_response(rsp);
    `uvm_info(get_type_name(), $sformatf("req_addr = 'h%0h, req_data = 'h%0h", 
        req.addr, req.data), UVM_HIGH)
    //`uvm_info(get_type_name(), $sformatf("rsp_addr = 'h%0h, rsp_data = 'h%0h", 
    //    rsp.addr, rsp.data), UVM_HIGH)
    endtask
endclass : read_byte_seq

// SEQUENCE: write_byte_seq
class write_byte_seq extends apb_master_base_seq;
  rand bit [31:0] start_addr;
  rand bit [7:0] write_data;
  rand int unsigned transmit_del;

  function new(string name="write_byte_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(write_byte_seq)

  constraint transmit_del_ct { (transmit_del <= 10); }
    
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    `uvm_do_with(req, 
      { req.addr == start_addr;
        req.direction == APB_WRITE;
        req.data == write_data;
        req.transmit_delay == transmit_del; } )
    `uvm_info(get_type_name(), $sformatf("addr = 'h%0h, data = 'h%0h", 
        req.addr, req.data), UVM_HIGH)
    endtask
endclass : write_byte_seq

//------------------------------------------------------------------------------
// SEQUENCE: read_word_seq
//------------------------------------------------------------------------------
class read_word_seq extends apb_master_base_seq;
  rand bit [31:0] start_addr;
  rand int unsigned transmit_del;

  function new(string name="read_word_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(read_word_seq)

  constraint transmit_del_ct { (transmit_del <= 10); }
  constraint addr_ct {(start_addr[1:0] == 0); }
    
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    `uvm_do_with(req, 
      { req.addr == start_addr;
        req.direction == APB_READ;
        req.transmit_delay == transmit_del; } ) 
    //get_response(rsp);
    `uvm_info(get_type_name(), $sformatf("req_addr = 'h%0h, req_data = 'h%0h", 
        req.addr, req.data), UVM_HIGH)
    `uvm_info(get_type_name(), $sformatf("rsp_addr = 'h%0h, rsp_data = 'h%0h", 
        rsp.addr, rsp.data), UVM_HIGH)
    endtask
endclass : read_word_seq

// SEQUENCE: write_word_seq
class write_word_seq extends apb_master_base_seq;
  rand bit [31:0] start_addr;
  rand bit [31:0] write_data;
  rand int unsigned transmit_del;

  function new(string name="write_word_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(write_word_seq)

  constraint transmit_del_ct { (transmit_del <= 10); }
  constraint addr_ct {(start_addr[1:0] == 0); }
    
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    `uvm_do_with(req, 
      { req.addr == start_addr;
        req.direction == APB_WRITE;
        req.data == write_data;
        req.transmit_delay == transmit_del; } )
    `uvm_info(get_type_name(), $sformatf("addr = 'h%0h, data = 'h%0h", 
        req.addr, req.data), UVM_HIGH)
    endtask
endclass : write_word_seq

// SEQUENCE: read_after_write_seq
class read_after_write_seq extends apb_master_base_seq;
//class read_after_write_seq extends uvm_sequence #(apb_transfer);

  rand bit [31:0] start_addr;
  rand bit [7:0] write_data;
  rand int unsigned transmit_del;

  function new(string name="read_after_write_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(read_after_write_seq)

  constraint transmit_del_ct { (transmit_del <= 10); }
  constraint addr_ct {(start_addr[1:0] == 0); }
    
  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_MEDIUM)
    `uvm_do_with(req, 
      { req.addr == start_addr;
        req.direction == APB_WRITE;
        req.data == write_data;
        req.transmit_delay == transmit_del; } )
    `uvm_do_with(req, 
      { req.addr == start_addr;
        req.direction == APB_READ;
        req.transmit_delay == transmit_del; } ) 
    `uvm_info(get_type_name(), $sformatf("addr = 'h%0h, data = 'h%0h", 
              req.addr, req.data), UVM_HIGH)
    endtask
  
endclass : read_after_write_seq

// SEQUENCE: multiple_read_after_write_seq
class multiple_read_after_write_seq extends apb_master_base_seq;

    read_after_write_seq raw_seq;
    rand int unsigned num_of_seq;

    function new(string name="multiple_read_after_write_seq");
      super.new(name);
    endfunction
  
    `uvm_object_utils(multiple_read_after_write_seq)

    constraint num_of_seq_c { num_of_seq <= 10; num_of_seq >= 5; }

    virtual task body();
      `uvm_info(get_type_name(), "Starting...", UVM_MEDIUM)
      for (int i = 0; i < num_of_seq; i++) begin
        `uvm_info(get_type_name(), $sformatf("Executing sequence # %0d", i),
                  UVM_HIGH)
        `uvm_do(raw_seq)
      end
    endtask
endclass : multiple_read_after_write_seq
`endif // APB_MASTER_SEQ_LIB_SV
