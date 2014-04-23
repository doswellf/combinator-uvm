/*-------------------------------------------------------------------------
File name   : apb_subsystem_rgm_master_sequencer.sv
Title       : Reg Mem Master sequencer
Project     :
Created     :
Description : Reg Mem master sequencer for APB Subsystem
Notes       : This master sequencer will override the ahb_master_sequencer
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
 
`uvm_blocking_put_imp_decl(_reg)

typedef class apb_subsystem_rgm_adapter_seq;

class apb_subsystem_rgm_master_sequencer extends ahb_pkg::ahb_master_sequencer;

   uvm_blocking_put_imp_reg #(uvm_rgm_reg_op, apb_subsystem_rgm_master_sequencer) reg_req_export;
   uvm_analysis_port #(uvm_rgm_reg_op) reg_rsp_port;
   apb_subsystem_rgm_adapter_seq adapter_seq;
   
   `uvm_sequencer_utils(apb_subsystem_rgm_master_sequencer)

   function new(string name, uvm_component parent);
      super.new(name, parent);
      reg_req_export = new("reg_req_export", this);
      reg_rsp_port = new("reg_rsp_port", this);
      `uvm_update_sequence_lib_and_item(ahb_pkg::ahb_transfer)
      adapter_seq = apb_subsystem_rgm_adapter_seq::type_id::create("adapter_seq", this);
   endfunction : new

   task run_phase(uvm_phase phase);
     adapter_seq.start(this);
     super.run_phase(phase);
   endtask

   task put_reg(uvm_rgm_reg_op t);
     adapter_seq.execute_op(t);
   endtask
endclass : apb_subsystem_rgm_master_sequencer

class user_reg_sequencer extends uvm_rgm_sequencer;
  `uvm_sequencer_utils(user_reg_sequencer)
  function new (string name, uvm_component parent);
    super.new(name, parent);
    `uvm_update_sequence_lib
  endfunction : new
endclass : user_reg_sequencer

//class apb_subsystem_rgm_adapter_seq extends uvm_sequence #(ahb_pkg::ahb_transfer);
class apb_subsystem_rgm_adapter_seq extends uvm_sequence #(ahb_transfer);
  
   uvm_rgm_reg_op cur_op;

   `uvm_sequence_utils(apb_subsystem_rgm_adapter_seq, apb_subsystem_rgm_master_sequencer)
  
   function new(string name="apb_subsystem_rgm_adapter_seq");
     super.new(name);
     req=new;
   endfunction : new
  
   virtual task body();
     process_responses();
   endtask

    virtual task process_responses();
      while (1) begin
        get_response(rsp);
        `uvm_info("apb_subsystem_rgm_adapter_seq", $sformatf("Received response is"), UVM_MEDIUM)
        rsp.print();
        p_sequencer.reg_rsp_port.write(cur_op);
      end
    endtask

    virtual task execute_op(uvm_rgm_reg_op op);
      bit [`AHB_ADDR_WIDTH-1:0] write_data;
      bit [`AHB_ADDR_WIDTH-1:0] read_data;

      `uvm_info("ex_rgm_adapter_seq", 
         $sformatf("Adapter sequence starting..."))
       case (op.get_direction())
         uvm_rgm_pkg::OP_RD : begin
         `uvm_do_with(req, { req.address == op.get_address(); req.data == read_data; req.direction == READ; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
         end
         uvm_rgm_pkg::OP_WR : begin
            write_data = op.get_reg_value();
            `uvm_do_with(req, { req.address == op.get_address(); req.data == write_data; req.direction == WRITE; req.burst == ahb_pkg::SINGLE; req.hsize == ahb_pkg::WORD;} )
         end
       endcase
    endtask

endclass
  
