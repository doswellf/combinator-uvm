
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
import uvm_ml::*;
`include "uvm_macros.svh"

//----------------------------------------------------------------------
// trans
//----------------------------------------------------------------------

typedef class ext1;
typedef ext1 ext1_ext;

// Generic payload extension
class ext1 extends uvm_tlm_extension#(ext1_ext);
   int a;
   `uvm_object_utils_begin(ext1)      
     `uvm_field_int(a, UVM_ALL_ON)
   `uvm_object_utils_end

  function new(string name="ext1");
     super.new(name);
  endfunction // new

   function void fill(int base);
      a = base;
   endfunction // fill

   function void check_data(ext1 expected);
      assert(a==expected.a);
   endfunction // check_data

endclass

// Generic payload with extension
class trans extends uvm_tlm_generic_payload;
  int unsigned f0;

  function string convert2string();
    return super.convert2string();
  endfunction

  `uvm_object_utils_begin(trans)
    `uvm_field_int(f0, UVM_ALL_ON);
  `uvm_object_utils_end 
endclass

// Serializer for extended generic payload
class ml_tlm2_trans_serializer extends uvm_ml::tlm_generic_payload_serializer;
  function string get_my_name();
    return "ml_tlm2_trans_serializer";
  endfunction
  function void serialize(uvm_object obj);
    trans inst;
    $cast(inst,obj);
    super.serialize(inst);

    pack_field_int(inst.f0, 32);
  endfunction

  function void deserialize(inout uvm_object obj);
    trans inst;
    super.deserialize(obj);
    $cast(inst,obj);

    inst.f0 = unpack_field_int(32);
  endfunction
endclass

// code for serializer registration
function int register_ml_tlm2_trans_serializer();
  ml_tlm2_trans_serializer inst;
  inst = new;
  return uvm_ml::register_class_serializer(inst,trans::get_type());
endfunction : register_ml_tlm2_trans_serializer
int dummy_register_ml_tlm2_trans_serializer = register_ml_tlm2_trans_serializer();


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
    ext1 e;
    trans expected;
     
    $display("[SV ",$realtime,"] consumer::b_transport");
    $cast(e, t.get_extension(ext1::ID()));
    $display("[SV ",$realtime,"] extension = ", e.a);
    #5000;
     expected = create_trans(transaction_count);
     check_data(expected,t);
    $display("[SV ",$realtime,"] consumer received", t.convert2string());
    transaction_count++;
  endtask

function void check_data(trans expected,  trans actual);
      
      byte unsigned d[];
      byte unsigned ed[];
   ext1 ext;
   ext1 expected_ext;
   
  
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
   
   $cast(ext, actual.get_extension(ext1::ID()));
    $cast(expected_ext, expected.get_extension(ext1::ID()));
   assert(ext != null);
    assert(expected_ext != null);
   ext.check_data(expected_ext);
   

   endfunction // check_that
   
   function trans create_trans(int unsigned base);
      byte unsigned data[];
      trans gp = new();
      ext1 ext = new();
      
      data = new[base+1];
      for(int unsigned i = 0; i < base+1; i++) begin
         data[i] = i;
      end
      
      gp.set_address(base*1000+base*100+base*10+base);
      gp.set_data_length(base+1);
      gp.set_data(data);
      gp.set_command(UVM_TLM_WRITE_COMMAND);
      ext.fill(base+1);
      void'(gp.set_extension(ext));
      
      return gp;
   endfunction // create_trans
   
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
//----------------------------------------------------------------------
class env extends uvm_component;

  `uvm_component_utils(env)

  consumer c;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void phase_ended(uvm_phase phase);
    if (phase.get_name() == "build") begin
      uvm_ml::ml_tlm2 #(trans)::register(c.target_socket);
    end
  endfunction

  function void build_phase(uvm_phase phase);
    c = new("consumer", this);
  endfunction

  function void connect_phase(uvm_phase phase);
     bit res;
     res = uvm_ml::connect("top.initiator.isocket",c.target_socket.get_full_name() );
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
      for (integer i   = 0; i < 100000; i++) begin
          uvm_ml::synchronize();
          #1;
      end
      phase.drop_objection(this);
  endtask

endclass

//----------------------------------------------------------------------
// top
//----------------------------------------------------------------------
module top1;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];

   tops[0] = "SC:top";
   uvm_ml_run_test(tops, "SV:test");
end // initial begin
`endif
endmodule
