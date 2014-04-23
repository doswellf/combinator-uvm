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
    `uvm_object_utils_begin(packet)
      `uvm_field_int(data, UVM_ALL_ON)
    `uvm_object_utils_end

    function void next();
      static int d = 101;
      data = d++;
    endfunction

    function int get_data();
      return data;
    endfunction

  endclass

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
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());

      $display("-- SV [%0t] : Raising objection in %s for 10NS", $time, phase.get_name());
      phase.raise_objection(this);
        #10;
      phase.drop_objection(this);
      $display("-- SV [%0t] : Dropping objection in %s ", $time, phase.get_name());
    endtask
  
  endclass


    // Subscriber class receives packetrs through its analysis export
    
  class subscriber #(type T=packet) extends uvm_component;
    uvm_analysis_imp #(T,subscriber #(T)) aimp;
  
    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      aimp=new("aimp",this);
    endfunction
  
    typedef subscriber#(T) this_type;
    `uvm_component_utils_begin(this_type)
    `uvm_component_utils_end
  
    function void write (T p);
      $display("[SV ",$realtime," ns] subscriber::write(",p.data,") ", get_full_name());
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
      $display("===== SV : build - %s", get_full_name());
      sub1 = new("subscriber1", this);
      sub2 = new("subscriber2", this);
      prod = new("producer", this);
    endfunction

    // Register ML ports at the end of build phase
    function void phase_ended(uvm_phase phase);
      $display("***** SV[%0t] : phase_ended for %s - %s", $realtime, phase.get_name(), get_full_name());
      if (phase.get_name() == "build") begin
        uvm_ml::ml_tlm1 #(packet)::register(sub1.aimp);
        uvm_ml::ml_tlm1 #(packet)::register(sub2.aimp);
      end
    endfunction

    function void phase_started(uvm_phase phase);
      $display("***** SV[%0t] : phase_started for %s - %s", $realtime, phase.get_name(), get_full_name());
    endfunction

    // Connect ports in connect phase
    function void connect();
      bit res;
      $display("===== SV : connect - %s", get_full_name());
      prod.aport.connect(sub1.aimp);
      prod.aport.connect(sub2.aimp);
      res = uvm_ml::connect("sctop.my_env.producer.aport", sub1.aimp.get_full_name());
      res = uvm_ml::connect("sctop.my_env.producer.aport1", sub2.aimp.get_full_name());
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endfunction

    function void extract_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endfunction

    function void check_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endfunction

    function void report_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endfunction

    function void final_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endfunction

    task reset_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
      $display("-- SV [%0t] : Raising objection in %s for 20NS", $time, phase.get_name());
      phase.raise_objection(this);
      #20;
      phase.drop_objection(this);
      $display("-- SV [%0t] : Dropping objection in %s ", $time, phase.get_name());
    endtask

    task configure_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endtask

    task main_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endtask

    task shutdown_phase(uvm_phase phase);
      $display("===== SV : %s - %s", phase.get_name(), get_full_name());
    endtask

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

    function void before_end_of_elaboration_phase(uvm_phase phase);
    $display("SV test : before_end_of_elaboration_phase");
    endfunction // void

      task run_phase(uvm_phase phase);
          for (integer i = 0; i < 100000; i++) begin
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
