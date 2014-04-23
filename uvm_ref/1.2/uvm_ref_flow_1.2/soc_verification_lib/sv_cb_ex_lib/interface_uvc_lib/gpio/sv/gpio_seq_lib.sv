/*-------------------------------------------------------------------------
File name   : gpio_seq_lib.sv
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


`ifndef GPIO_SEQ_LIB_SV
`define GPIO_SEQ_LIB_SV

class gpio_simple_trans_seq extends uvm_sequence #(gpio_transfer);

  function new(string name="gpio_simple_trans_seq");
    super.new(name);
  endfunction
  
  `uvm_object_utils(gpio_simple_trans_seq)    
  `uvm_declare_p_sequencer(gpio_sequencer)

  rand int unsigned del = 0;
  constraint del_ct { (del <= 10); }

  virtual task body();
    `uvm_info("GPIO_SEQ", $sformatf("Doing gpio_simple_trans_seq Sequence"), UVM_HIGH)
    `uvm_do_with(req, {req.delay == del;} )
  endtask
  
endclass : gpio_simple_trans_seq

class gpio_multiple_simple_trans extends uvm_sequence #(gpio_transfer);

    rand int unsigned cnt_i;

    gpio_simple_trans_seq simple_trans;

    function new(string name="gpio_multiple_simple_trans");
      super.new(name);
    endfunction

   // register sequence with a sequencer 
   `uvm_object_utils(gpio_multiple_simple_trans)    
   `uvm_declare_p_sequencer(gpio_sequencer)

    constraint count_ct {cnt_i <= 10;}

    virtual task body();
      for (int i = 0; i < cnt_i; i++)
      begin
        `uvm_do(simple_trans)
      end
    endtask
endclass: gpio_multiple_simple_trans

`endif // GPIO_SEQ_LIB_SV

