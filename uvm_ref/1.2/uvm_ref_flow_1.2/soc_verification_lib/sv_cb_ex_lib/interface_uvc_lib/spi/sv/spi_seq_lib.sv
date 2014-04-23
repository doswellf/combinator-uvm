/*-------------------------------------------------------------------------
File name   : spi_seq_lib.sv
Title       : SPI SystemVerilog UVM UVC
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


`ifndef SPI_SEQ_LIB_SV
`define SPI_SEQ_LIB_SV

class trans_seq extends uvm_sequence #(spi_transfer);

  function new(string name="trans_seq");
    super.new(name);
  endfunction
  
  `uvm_object_utils(trans_seq)    
  `uvm_declare_p_sequencer(spi_sequencer)

  rand int unsigned del = 0;
  constraint del_ct { (del <= 10); }

  virtual task body();
    `uvm_info("SPI_SEQ", $sformatf("Doing trans_seq Sequence"), UVM_HIGH)
    `uvm_do_with(req, {req.delay == del;} )
  endtask
  
endclass : trans_seq

class spi_incr_payload extends uvm_sequence #(spi_transfer);

    rand int unsigned cnt_i;
    rand bit [7:0] start_payload;

    function new(string name="spi_incr_payload");
      super.new(name);
    endfunction
   // register sequence with a sequencer 
   `uvm_object_utils(spi_incr_payload)
   `uvm_declare_p_sequencer(spi_sequencer)

    constraint count_ct {cnt_i <= 10;}

    virtual task body();
      for (int i = 0; i < cnt_i; i++)
      begin
        `uvm_do_with(req, {req.transfer_data == (start_payload +i*3)%256; })
      end
    endtask
endclass: spi_incr_payload

`endif // SPI_SEQ_LIB_SV

