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

// Test demonstrates hierarchical construction
// SV is the top component and it creates an SC subtree from its env

import uvm_pkg::*;
`include "uvm_macros.svh"
 import uvm_ml::*;

`include "producer.sv"
`include "consumer.sv"
    

  // The environment contains one instance of the producer and 
  // one instance of the consumer
  class env extends uvm_env;
    producer prod;
    consumer cons;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),$sformatf("SV env::new %s", name),UVM_LOW);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV env::build"),UVM_LOW);
      cons = consumer::type_id::create("consumer", this);
      prod = producer::type_id::create("producer", this);
    endfunction
   
    // Connect ports in connect phase
    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV env::connect %s", get_full_name()),UVM_LOW);
    endfunction

    function void resolve_bindings();
      `uvm_info(get_type_name(),$sformatf("SV env::resolve_bindings %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void end_of_elaboration();
      `uvm_info(get_type_name(),$sformatf("SV env::end_of_elaboration %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void start_of_simulation();
      `uvm_info(get_type_name(),$sformatf("SV env::start_of_simulation %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void extract_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV env::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction
  
    function void check_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV env::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV env::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    function void final_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV env::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    `uvm_component_utils(env)

  endclass


    
  // Testbench component instantiating a remote SC sub-tree
  class testbench extends uvm_env;
    uvm_component sctop;

    `uvm_component_utils(testbench)

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),$sformatf("SV env::new %s", name),UVM_LOW);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV testbench::build"),UVM_LOW);
      // create ML junction node in SystemC
      sctop = uvm_ml_create_component("SC", "sctop", "sctop", this);
    endfunction // void

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV testbench::connect %s", get_full_name()),UVM_LOW);
    endfunction

    function void resolve_bindings();
      `uvm_info(get_type_name(),$sformatf("SV testbench::resolve_bindings %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void end_of_elaboration();
      `uvm_info(get_type_name(),$sformatf("SV testbench::end_of_elaboration %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void start_of_simulation();
      `uvm_info(get_type_name(),$sformatf("SV testbench::start_of_simulation %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void extract_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV testbench::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction
  
    function void check_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV env::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV testbench::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    function void final_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV testbench::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

  endclass 

    
  // Test instantiates the "env" and "testbench" which has a foreign child
  class test extends uvm_env;
    env sv_env;
    testbench tb;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),$sformatf("SV test::new %s", get_full_name()),UVM_LOW);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);      
      `uvm_info(get_type_name(),$sformatf("SV test::build %s", get_full_name()),UVM_LOW);
      set_config_int("*prod*","address", ($urandom() & 'hffff));
      sv_env = env::type_id::create("sv_env", this);
      tb = testbench::type_id::create("testbench", this);
    endfunction
   
    function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") begin
	 `uvm_info(get_type_name(),$sformatf("SV test registered %s", sv_env.cons.b_target_socket.get_full_name()),UVM_LOW);
         uvm_ml::ml_tlm2#()::register(sv_env.cons.b_target_socket);
	 `uvm_info(get_type_name(),$sformatf("SV test registered %s", sv_env.cons.nb_target_socket.get_full_name()),UVM_LOW);
         uvm_ml::ml_tlm2#()::register(sv_env.cons.nb_target_socket);
	 `uvm_info(get_type_name(),$sformatf("SV test registered %s", sv_env.prod.b_initiator_socket.get_full_name()),UVM_LOW);
         uvm_ml::ml_tlm2#()::register(sv_env.prod.b_initiator_socket);
	 `uvm_info(get_type_name(),$sformatf("SV test registered %s", sv_env.prod.nb_initiator_socket.get_full_name()),UVM_LOW);
         uvm_ml::ml_tlm2#()::register(sv_env.prod.nb_initiator_socket);
      end
    endfunction

    function void connect_phase(uvm_phase phase);
      string sc_producer = "uvm_test_top.testbench.sctop.sc_env.prod.";
      string sc_consumer = "uvm_test_top.testbench.sctop.sc_env.cons.";
      super.connect_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV test::connect %s", get_full_name()),UVM_LOW);
      if(!uvm_ml::connect({sc_producer, "b_isocket"}, sv_env.cons.b_target_socket.get_full_name())) begin
	 `uvm_info(get_type_name(),$sformatf("SV test::connect failed %s", sv_env.cons.b_target_socket.get_full_name()),UVM_LOW);
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({sc_producer, "nb_isocket"}, sv_env.cons.nb_target_socket.get_full_name())) begin
	 `uvm_info(get_type_name(),$sformatf("SV test::connect failed %s", sv_env.cons.nb_target_socket.get_full_name()),UVM_LOW);
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod.b_initiator_socket.get_full_name(), {sc_consumer, "tsocket"})) begin
	 `uvm_info(get_type_name(),$sformatf("SV test::connect failed %s", sv_env.prod.b_initiator_socket.get_full_name()),UVM_LOW);
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod.nb_initiator_socket.get_full_name(), {sc_consumer, "tsocket"})) begin
	 `uvm_info(get_type_name(),$sformatf("SV test::connect failed %s", sv_env.prod.nb_initiator_socket.get_full_name()),UVM_LOW);
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
    endfunction
   
    function void resolve_bindings();
      `uvm_info(get_type_name(),$sformatf("SV test::resolve_bindings %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void end_of_elaboration();
      `uvm_info(get_type_name(),$sformatf("SV test::end_of_elaboration %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void start_of_simulation();
      `uvm_info(get_type_name(),$sformatf("SV test::start_of_simulation %s", get_full_name()),UVM_LOW);
    endfunction
   
    task run_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV test::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
      while (1) begin
         #1 uvm_ml::synchronize();
      end    
    endtask
   
    function void extract_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV test::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction
  
    function void check_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV test::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV test::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    function void final_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("SV test::%s %s", phase.get_name(), get_full_name()),UVM_LOW);
    endfunction

    `uvm_component_utils(test)
  endclass    

    
module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];
   
   tops[0] = "";
   
   uvm_ml_run_test(tops, "SV:test");
end
`endif
endmodule
