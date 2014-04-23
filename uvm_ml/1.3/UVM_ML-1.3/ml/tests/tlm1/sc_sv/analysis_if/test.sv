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

// Test demonstrates concurrent TLM1 communication between SC and SV in 
// both directions

module topmodule;
import uvm_pkg::*;
import uvm_ml::*;
   
`include "uvm_macros.svh"
   
class packet extends uvm_transaction;
   int    data;
   bit 	  kind;

   `uvm_object_utils_begin(packet)
     `uvm_field_int(data, UVM_ALL_ON)
       `uvm_field_int(kind, UVM_ALL_ON)
       `uvm_object_utils_end
	 
	 function void next();
	    static int d = 101;
	    data = d++;
	 endfunction
   
   function int get_data();
      return data;
   endfunction // get_data

   function void set_kind();
      kind = 1;
   endfunction // set_kind
   
   
   function bit check_data(int d);
      if (data == d)
	return 1;
      else
	return 0;
   endfunction // check_data

endclass // packet

   // Producer class sends 5 packets (101-105) through the analysis port
   // The port is bound to 2 instances of the subscriber
    
class producer #(type T=packet) extends uvm_component;
    uvm_analysis_port #(T) aport;
  
    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      aport=new("aport",this);
    endfunction
  
    typedef producer#(T) this_type;
    `uvm_component_utils_begin(this_type)
    `uvm_component_utils_end

    task run_phase (uvm_phase phase);
       T p;
       phase.raise_objection(this);
        p = new();
       p.set_kind();
        p.next();

        $display("[SV ",$realtime, " ns] producer::run, writing ", p.get_data());
       aport.write(p);
        #10;
        p.next();
        $display("[SV ",$realtime, " ns] producer::run, writing ", p.get_data());
        aport.write(p);
        #10;
        p.next();
        $display("[SV ",$realtime, " ns] producer::run, writing ", p.get_data());
        aport.write(p);
        #10;
        p.next();
        $display("[SV ",$realtime, " ns] producer::run, writing ", p.get_data());
        aport.write(p);
        #10;
        p.next();
        $display("[SV ",$realtime, " ns] producer::run, writing ", p.get_data());
        aport.write(p);
        #10;
        phase.drop_objection(this);
       
    endtask
  
  endclass


    // Subscriber class receives packetrs through its analysis export
    
  class subscriber #(type T=packet) extends uvm_component;
     int expected_sv;
     int expected_sc;
     
    uvm_analysis_imp #(T,subscriber #(T)) aimp;
     
    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      aimp=new("aimp",this);
       expected_sv = 101;
       expected_sc = 17;
    endfunction
  
    typedef subscriber#(T) this_type;
    `uvm_component_utils_begin(this_type)
    `uvm_component_utils_end
  
    function void write (T p);
      $display("[SV ",$realtime," ns] subscriber::write(",p.data,") ", get_full_name());
       if (p.kind == 1) begin
	  assert(p.data == expected_sv);
	  expected_sv++;
       end
       if (p.kind == 0) begin
	  assert(p.data == expected_sc);
	  expected_sc++;
       end
       $display("");
    endfunction 
  
  endclass


    // The environment contains one instance of the producer and 
    // 2 instances of the subscriber
    // The analysis exports are registered as ML and connected to the SC ports
    
  class env extends uvm_env;
    subscriber #(packet) sub1;
    subscriber #(packet) sub2;
    producer #(packet) prod;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
    endfunction

    function void build();
      super.build();
      sub1 = new("subscriber1", this);
      sub2 = new("subscriber2", this);
      prod = new("producer", this);
    endfunction

    // Register ML ports at the end of build phase
    function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") begin
        uvm_ml::ml_tlm1 #(packet)::register(sub1.aimp);
        uvm_ml::ml_tlm1 #(packet)::register(sub2.aimp);
      end
    endfunction

    // Connect ports in connect phase
    function void connect();
      bit res;
      prod.aport.connect(sub1.aimp);
      prod.aport.connect(sub2.aimp);
      res = uvm_ml::connect("sctop.producer.aport", sub1.aimp.get_full_name());
      res = uvm_ml::connect("sctop.producer.aport1", sub2.aimp.get_full_name());
    endfunction

    `uvm_component_utils(env)

  endclass    


    // Test instantiates the "env"
    
  class test extends uvm_env;
    env top_env;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
    endfunction

    function void build();
      super.build();
      top_env = new("top_env", this);
    endfunction // void

      task run_phase(uvm_phase phase);
      while(1) begin
          //for (integer i = 0; i < 100000; i++) begin
	      #1 uvm_ml::synchronize();
          end;      
          
      endtask
    `uvm_component_utils(test)
  endclass // test
`ifdef USE_UVM_ML_RUN_TEST 
initial begin
   string tops[2];

   tops[0] = "SV:test";
   tops[1] = "SC:sctop";

   uvm_ml_run_test(tops, "");
end
`endif
endmodule
