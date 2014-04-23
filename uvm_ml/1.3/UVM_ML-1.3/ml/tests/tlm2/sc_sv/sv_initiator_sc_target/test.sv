//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
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
import uvm_pkg::*;
`include "uvm_macros.svh"
import uvm_ml::*;

//----------------------------------------------------------------------
// producer
//----------------------------------------------------------------------
class producer extends uvm_component;

  uvm_tlm_nb_initiator_socket #(producer) initiator_socket;

  bit done;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build();
    initiator_socket = new("initator_socket", this);
  endfunction

  function uvm_tlm_sync_e nb_transport_bw(uvm_tlm_generic_payload t,
                                      ref uvm_tlm_phase_e p,
                                      input uvm_tlm_time delay);
    uvm_report_warning("producer", "nb_transport_bw is not implemented");
  endfunction

  task run_phase(uvm_phase phase);

    int unsigned i;
    uvm_tlm_time delay = new;
    uvm_tlm_phase_e ph;
    uvm_tlm_sync_e sync;
    uvm_tlm_generic_payload t;

    phase.raise_objection(this);

    delay.incr(1, 1ns);

    for(i = 0; i < 10; i++) begin
       t = generate_transaction(i);
       $display("[SV ",$realtime,"] producer sending", t.convert2string());
       sync = initiator_socket.nb_transport_fw(t, ph, delay);
       assert(sync == UVM_TLM_ACCEPTED);
    end

    phase.drop_objection(this);
  endtask

  //--------------------------------------------------------------------
  // generate_transaction
  //
  // generate a new, none random transaction
  //--------------------------------------------------------------------
  function uvm_tlm_generic_payload generate_transaction(int base);

    bit [63:0] addr;
    int unsigned length;
    byte unsigned data[];

    uvm_tlm_generic_payload t = new();
     addr = base;
    length = base;
    data = new[length];

    t.set_data_length(length);
    t.set_address(addr);

    for(int unsigned i = 0; i < length; i++) begin
      data[i] = base+i;
    end
    
    t.set_data(data);
    t.set_command(UVM_TLM_WRITE_COMMAND);

    return t;
  endfunction

endclass


//----------------------------------------------------------------------
// env
//----------------------------------------------------------------------
class env extends uvm_component;

  `uvm_component_utils(env)

  producer p;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build();
    p = new("producer", this);
  endfunction

  function void phase_ended(uvm_phase phase);
    if (phase.get_name() == "build") begin
      uvm_ml::ml_tlm2#()::register(p.initiator_socket);
    end
  endfunction

  function void connect();
    bit result = uvm_ml::connect(p.initiator_socket.get_full_name(), "top.t.tsocket");
  endfunction

endclass

//----------------------------------------------------------------------
// test
//----------------------------------------------------------------------
class test extends uvm_component;

  `uvm_component_utils(test)

  env e;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build();
    e = new("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    for (int i = 0; i < 1000; i++) begin
        uvm_ml::synchronize();
        #1;
    end
    phase.drop_objection(this);
  endtask
endclass

//----------------------------------------------------------------------
// top
//----------------------------------------------------------------------
module svtop;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];

   
   tops[0] = "SC:top";

   uvm_ml_run_test(tops, "SV:test");
end
`endif
endmodule
