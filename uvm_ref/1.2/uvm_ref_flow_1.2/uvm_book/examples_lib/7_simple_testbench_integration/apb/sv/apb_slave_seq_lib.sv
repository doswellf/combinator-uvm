/*******************************************************************************
  FILE : apb_slave_seq_lib.sv
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


`ifndef APB_SLAVE_SEQ_LIB_SV
`define APB_SLAVE_SEQ_LIB_SV

//------------------------------------------------------------------------------
// SEQUENCE: simple_response_seq
//------------------------------------------------------------------------------

class simple_response_seq extends uvm_sequence #(apb_transfer);

  function new(string name="simple_response_seq");
    super.new(name);
  endfunction

  `uvm_object_utils(simple_response_seq)
  `uvm_declare_p_sequencer(apb_slave_sequencer)

  apb_transfer req;
  apb_transfer util_transfer;

  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_MEDIUM)
    forever begin
      p_sequencer.addr_trans_port.peek(util_transfer);
      if((util_transfer.direction == APB_READ) && 
        (p_sequencer.cfg.check_address_range(util_transfer.addr) == 1)) begin
        `uvm_info(get_type_name(), $sformatf("Address:%h Range Matching read.  Responding...", util_transfer.addr), UVM_MEDIUM);
        `uvm_do_with(req, { req.direction == APB_READ; } )
      end
    end
  endtask : body

endclass : simple_response_seq

//------------------------------------------------------------------------------
// SEQUENCE: mem_response_seq
//------------------------------------------------------------------------------
class mem_response_seq extends uvm_sequence #(apb_transfer);

  function new(string name="mem_response_seq");
    super.new(name);
  endfunction

  rand logic [7:0] mem_data;

  `uvm_object_utils(mem_response_seq)
  `uvm_declare_p_sequencer(apb_slave_sequencer)

  //simple assoc array to hold values
  logic [7:0] slave_mem[int];

  apb_transfer req;
  apb_transfer util_transfer;

  virtual task body();
    `uvm_info(get_type_name(), "Starting...", UVM_MEDIUM)
    forever begin
      p_sequencer.addr_trans_port.peek(util_transfer);
      if((util_transfer.direction == APB_READ) && 
        (p_sequencer.cfg.check_address_range(util_transfer.addr) == 1)) begin
        `uvm_info(get_type_name(), $sformatf("Address:%h Range Matching APB_READ.  Responding...", util_transfer.addr), UVM_MEDIUM);
        if (slave_mem.exists(util_transfer.addr))
        `uvm_do_with(req, { req.direction == APB_READ;
                            req.addr == util_transfer.addr;
                            req.data == slave_mem[util_transfer.addr]; } )
        else  begin
        `uvm_do_with(req, { req.direction == APB_READ;
                            req.addr == util_transfer.addr;
                            req.data == mem_data; } )
         mem_data++; 
        end
      end
      else begin
        if (p_sequencer.cfg.check_address_range(util_transfer.addr) == 1) begin
        slave_mem[util_transfer.addr] = util_transfer.data;
        // DUMMY response with same information
        `uvm_do_with(req, { req.direction == APB_WRITE;
                            req.addr == util_transfer.addr;
                            req.data == util_transfer.data; } )
       end
      end
    end
  endtask : body

endclass : mem_response_seq

`endif // APB_SLAVE_SEQ_LIB_SV
