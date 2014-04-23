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

class packet extends uvm_transaction;
   int    data;
   int    trailer;
   string txt;
   `uvm_object_utils_begin(packet)
     `uvm_field_int(data, UVM_ALL_ON)
     `uvm_field_int(trailer, UVM_ALL_ON)
     `uvm_field_string(txt, UVM_ALL_ON)
   `uvm_object_utils_end
endclass // packet


class monitor extends uvm_component;
   uvm_get_imp #(packet, monitor) b_in;

   `uvm_component_utils(monitor)
   
   packet cur_p;
   int call_index;
   
   function new (string name, uvm_component parent);
      super.new(name,parent);
      b_in = new("b_in", this);
      call_index = 1;      
   endfunction // new
   
   //get functions
   virtual task get(output packet obj);
      string exp_txt;
      `uvm_info(get_type_name(),"get started",UVM_LOW);
      obj = new;   
      obj.data = call_index * 10;
      obj.trailer = call_index * 20;
      obj.txt = $psprintf("Iteration # %0d",call_index);
      `uvm_info(get_type_name(),
		$sformatf("will return packet with data = %0d trailer = %0d txt = %s",obj.data,obj.trailer,obj.txt), 
		UVM_LOW);
      call_index++;
      #20;
      `uvm_info(get_type_name(),"get ended",UVM_LOW);
   endtask // get

   virtual function bit try_get(output packet obj);
      string exp_txt;
      `uvm_info(get_type_name(),"try_get started",UVM_LOW);
      if ( call_index <= 10 ) 
	begin
           obj = new;   
           obj.data = call_index * 10;
           obj.trailer = call_index * 20;
           obj.txt = $psprintf("Iteration # %0d",call_index);
	   `uvm_info(get_type_name(),
		     $sformatf("will return packet with data = %0d trailer = %0d txt = %s",obj.data,obj.trailer,obj.txt), 
		     UVM_LOW);
	   call_index++;
           try_get = 1;
	end else begin
	   try_get = 0;      
	end // else: !if( call_index <= 10 )
      `uvm_info(get_type_name(),$sformatf("try_get ended. result is %b",try_get),UVM_LOW);
   endfunction // try_get

   bit last_answer;
   
   virtual function bit can_get();
      can_get = !last_answer;
      `uvm_info(get_type_name(),$sformatf("going to return %d",can_get),UVM_LOW);
      last_answer = can_get;   
   endfunction // bit
      
   function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") 
	begin
	   uvm_ml::ml_tlm1 #(packet)::register(b_in,"packet");
       	end
   endfunction // phase_ended
   
   virtual function void build();
      super.build();
      `uvm_info(get_type_name(),"build()",UVM_LOW);
   endfunction // build
   
   virtual function void connect();
      //connection is done from e side
   endfunction // connect
   
endclass // monitor

class env extends uvm_env;
   
   `uvm_component_utils(env)

   monitor t;

   function new (string name, uvm_component parent);
      super.new(name,parent);
   endfunction // new
   
   function void build();
      super.build();
      `uvm_info(get_type_name(),"build()",UVM_LOW);
      t = new("monitor", this);
   endfunction // build
  
endclass // env


class test extends uvm_component;
   `uvm_component_utils(test)
   
   env top_env;

   function new (string name, uvm_component parent);
      super.new(name,parent);
   endfunction // new
   
   function void build();
      super.build();
      `uvm_info(get_type_name(),"build()",UVM_LOW);
      top_env = new("top_env", this);
   endfunction // build

   task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      #1000 phase.drop_objection(this);
   endtask // run_phase
   
endclass // test
   
module top;
`ifdef USE_UVM_ML_RUN_TEST
   initial
     begin
	string tops[2];
	tops[0] = "SV:test";
	tops[1] = "E:top.e";
	   
	uvm_ml_run_test(tops,"");
     end
`endif   
endmodule
