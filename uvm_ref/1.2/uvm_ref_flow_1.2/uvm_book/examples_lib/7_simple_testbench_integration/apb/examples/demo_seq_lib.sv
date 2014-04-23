/*******************************************************************************
  FILE : demo_seq_lib.sv
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


`ifndef DEMO_SEQ_LIB_SV
`define DEMO_SEQ_LIB_SV

//------------------------------------------------------------------------------
// SEQUENCE LIBRARY: demo_seq_lib
//------------------------------------------------------------------------------
// SEQUENCE: write_byte_seq
// SEQUENCE: read_byte_seq
// SEQUENCE: read_word_seq
// SEQUENCE: write_word_seq
// SEQUENCE: read_after_write_seq
// SEQUENCE: multiple_read_after_write_seq
//-------------------------------------------------------------------
class demo_seq_lib extends uvm_sequence_library #(apb_transfer);

  `uvm_object_utils(demo_seq_lib)
  `uvm_sequence_library_utils(demo_seq_lib)

  function new(string name="demo_seq_lib");
    super.new(name);
    // built-in fields
    min_random_count = 1;
    max_random_count = 5;
    // add sequences for this library
    add_sequence(write_byte_seq::get_type());
    add_sequence(read_byte_seq::get_type());
    add_sequence(read_after_write_seq::get_type());
    add_sequence(multiple_read_after_write_seq::get_type());
    //add_typewide_sequence(write_byte_seq::get_type());
    //add_typewide_sequence(read_byte_seq::get_type());
    //add_typewide_sequence(read_after_write_seq::get_type());
    //add_typewide_sequence(multiple_read_after_write_seq::get_type());
    init_sequence_library();
  endfunction

  task body();
    this.print();
    super.body();
    this.print();
  endtask : body
 
endclass : demo_seq_lib

class demo_seq_lib2 extends demo_seq_lib;

  `uvm_object_utils(demo_seq_lib2)
  `uvm_sequence_library_utils(demo_seq_lib2)

  function new(string name="demo_seq_lib2");
    super.new(name);
    // built-in fields
    min_random_count = 3;
    max_random_count = 8;
    // remove sequence for this library extension
    remove_sequence(multiple_read_after_write_seq::get_type());
    //init_sequence_library();
  endfunction

  task body();
   fork
    super.body();
    #800 remove_sequence(read_after_write_seq::get_type());
    #1000 add_sequence(multiple_read_after_write_seq::get_type());
   join
  endtask : body

endclass : demo_seq_lib2
`endif // DEMO_SEQ_LIB_SV
