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

`include "uvm_macros.svh"

import uvm_pkg::*;
import uvm_ml::*;

//----------------------------------------------------------------------
// trans
// adding printing method to generic payload
//----------------------------------------------------------------------
class trans extends uvm_tlm_generic_payload;

   function string convert2string();
      return super.convert2string();
   endfunction

  `uvm_object_utils_begin(trans)
  `uvm_object_utils_end 
endclass

// serializer method 
class trans_serializer extends uvm_ml::tlm_generic_payload_serializer;
    function string get_my_name();
        return "trans_serializer";
    endfunction
    function void serialize(uvm_object obj);
        super.serialize(obj);
        // in this test trans has no own fields
    endfunction
    function void deserialize(inout uvm_object obj);
        super.deserialize(obj);
    endfunction
    static function int register();
        static trans_serializer s;
        if (s == null) begin
           s = new;
           return uvm_ml::register_class_serializer(s, trans::get_type());
        end
        else
           return (-1);
    endfunction
endclass

int dummy_serializer = trans_serializer::register();

//----------------------------------------------------------------------
// producer
//----------------------------------------------------------------------
class producer extends uvm_component;

   uvm_tlm_b_initiator_socket #(trans) initiator_socket;
   
   local bit done;

   function new(string name, uvm_component parent);
      super.new(name, parent);
      done = 0;
      enable_stop_interrupt = 1;
   endfunction
   
   function void build_phase(uvm_phase phase);
      initiator_socket = new("initator_socket", this);
   endfunction
   
   task run_phase(uvm_phase phase);

    int unsigned i;
      realtime ctime;
    uvm_tlm_time delay = new;
    trans t;

    for(i = 0; i < 10; i++) begin
      t = generate_transaction(i);
      uvm_report_info("producer", t.convert2string());
       ctime = $realtime;
      initiator_socket.b_transport(t, delay);
       assert($realtime==ctime+5);
    end

    done = 1;
  endtask

  task stop(string ph_name);
    wait(done == 1);
  endtask

  function trans generate_transaction(int base);

    bit [63:0] addr;
    int unsigned length;
    byte unsigned data[];

    trans t = new();
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
// consumer
//----------------------------------------------------------------------
class consumer extends uvm_component;

   uvm_tlm_b_target_socket #(consumer, trans) target_socket;

   int unsigned transaction_count;

   function new(string name, uvm_component parent);
     super.new(name, parent);
     transaction_count = 0;
   endfunction

  function void build_phase(uvm_phase phase);
     target_socket = new("target_socket", this, this);
  endfunction

   task b_transport(trans t, uvm_tlm_time delay);
      trans expected;
      #5;
      expected =  generate_transaction(transaction_count);
     uvm_report_info("consumer", t.convert2string());
      check_data(expected,t);
     transaction_count++;
   endtask // b_transport
   
   function trans generate_transaction(int base);

    bit [63:0] addr;
    int unsigned length;
    byte unsigned data[];

    trans t = new();
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
   endfunction // generate_transaction
   
  function void check_data(trans expected,  trans actual);
      
      byte unsigned d[];
      byte unsigned ed[];
      
      if(expected.get_address() != actual.get_address()) begin
	 $display("expected address ",expected.get_address()," actual address is ",actual.get_address());
	 assert(0);
      end
      
      if(expected.get_command() != actual.get_command()) begin
	 $display("expected command ",expected.get_command()," actual command is ",actual.get_command());
	 assert(0);
      end

       if(expected.get_data_length() != actual.get_data_length()) begin
	 $display("expected data_length ",expected.get_data_length()," actual data_length is ",actual.get_data_length());
	 assert(0);
       end
      
      expected.get_data(ed);
      actual.get_data(d);
      if(ed != d) begin
	 $display("expected data[0] ",ed[0]," actual data[0] is ",d[0]);
	 assert(0);
      end
      
   endfunction // check_that

  function void report_phase(uvm_phase phase);
    if(transaction_count == 10)
      $display("** UVM TEST PASSED **");
    else
      $display("** UVM TEST FAILED **");
     assert(transaction_count == 10);
  endfunction

endclass

//----------------------------------------------------------------------
// env
// contains the producer and consumer
//----------------------------------------------------------------------


class env extends uvm_component;

   `uvm_component_utils(env)

   producer p;
   consumer c;

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

  function void phase_ended(uvm_phase phase);
    if (phase.get_name() == "build") begin
      uvm_ml::ml_tlm2 #(trans)::register(c.target_socket);
      uvm_ml::ml_tlm2 #(trans)::register(p.initiator_socket);
    end
  endfunction

  function void build_phase(uvm_phase phase);
    p = new("producer", this);
    c = new("consumer", this);
  endfunction

  // Bind the initiator socket to the target socket
  function void connect_phase(uvm_phase phase);
    bit result = uvm_ml::connect(p.initiator_socket.get_full_name(), c.target_socket.get_full_name());
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

  function void build_phase(uvm_phase phase);
    e = new("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    #100;
    phase.drop_objection(this);
  endtask

endclass

//----------------------------------------------------------------------
// top
//----------------------------------------------------------------------
module top;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
    string tops[1];
    tops[0]   = "";
    

    uvm_ml_run_test(tops, "SV:test");
end
`endif
endmodule
