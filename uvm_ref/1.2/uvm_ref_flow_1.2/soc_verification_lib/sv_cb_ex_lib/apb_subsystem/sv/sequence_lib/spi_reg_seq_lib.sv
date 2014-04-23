/*-------------------------------------------------------------------------
File name   : spi_reg_seq_lib.sv
Title       : REGMEM Sequence Library
Project     :
Created     :
Description : This file implements regmem sequences
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
 
class spi_cfg_reg_seq extends uvm_sequence;

   `uvm_object_utils(spi_cfg_reg_seq)

   function new(string name="spi_cfg_reg_seq");
      super.new(name);
   endfunction // new
 
   rand int spi_inst;
   string spi_rf;

   spi_regfile reg_model;

   virtual task body();
     uvm_status_e status;
      $sformat(spi_rf, "spi%0d_rf", spi_inst);
      `uvm_info("ex_reg_rw_reg_seq", 
        $sformatf("complete random spi configuration register sequence starting..."), UVM_MEDIUM)
      #200;
      reg_model.spi_ctrl.write(status, 16'h3E08);
      reg_model.spi_divider.write(status, 16'b1);
      reg_model.spi_ss.write(status, 8'b1);
      #50;
   endtask

endclass : spi_cfg_reg_seq

class spi_en_tx_reg_seq extends uvm_sequence;

   `uvm_object_utils(spi_en_tx_reg_seq)

   function new(string name="spi_en_tx_reg_seq");
      super.new(name);
   endfunction // new
 
   rand int spi_inst;
   string spi_rf;

   spi_regfile reg_model;

   virtual task body();
     uvm_status_e status;
      $sformat(spi_rf, "spi%0d_rf", spi_inst);
      `uvm_info("ex_reg_rw_reg_seq", 
        $sformatf("complete random spi configuration register sequence starting..."), UVM_MEDIUM)
      #200;
      reg_model.spi_ctrl.write(status, 16'h3F08);
      #50;
   endtask

endclass : spi_en_tx_reg_seq

