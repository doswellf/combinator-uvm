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
// SV is the top component and it creates an e subtree

import uvm_pkg::*;
`include "uvm_macros.svh"
 import uvm_ml::*;

`include "producer.sv"
`include "consumer.sv"
`include "env.sv"

  class svtop extends uvm_test;
    uvm_component e_env;
    sv_env  local_env;
    boolean e_active;
    boolean sv_active;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),$sformatf("SV svtop::new %s", name),UVM_LOW);
      e_active  = TRUE; // e has producer
      sv_active = TRUE; // SV has producer
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV svtop::build"),UVM_LOW);
      set_config_int("*producer","address", ($urandom() & 'hffff));
      set_config_int("*env","e_active",e_active);
      set_config_int("*env","sv_active",sv_active);

      // create local SV env
      local_env = sv_env::type_id::create("sv_env", this);
      // create remote ML junction node in e
      e_env = uvm_ml_create_component("e", "env", "e_env", this);
    endfunction // void

    // Register ML sockets
    function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") begin
	 if(sv_active == TRUE) begin
            uvm_ml::ml_tlm2#()::register(local_env.prod.b_initiator_socket);
            uvm_ml::ml_tlm2#()::register(local_env.prod.nb_initiator_socket);
	 end;
	 if(e_active == TRUE) begin
            uvm_ml::ml_tlm2#()::register(local_env.cons.b_target_socket);
            uvm_ml::ml_tlm2#()::register(local_env.cons.nb_target_socket);
	 end;
      end
    endfunction

    // Connect sockets
    function void connect_phase(uvm_phase phase);
      string e_consumer = "uvm_test_top.e_env.consumer.";
      string e_producer = "uvm_test_top.e_env.ACTIVE'producer.";
      string sv_consumer = "uvm_test_top.sv_env.consumer.";
      super.connect_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV svtop::connect %s", get_full_name()),UVM_LOW);
      
      if(sv_active == TRUE) begin
	 if(!uvm_ml::connect(local_env.prod.b_initiator_socket.get_full_name(), {e_consumer, "b_tsocket"})) begin
            `uvm_info(get_type_name(),$sformatf("SV svtop::connect failed %s", local_env.prod.b_initiator_socket.get_full_name()),UVM_LOW);
	    `uvm_fatal("MLCONN", "uvm_ml connect failed");
	 end;
	 if(!uvm_ml::connect(local_env.prod.nb_initiator_socket.get_full_name(), {e_consumer, "nb_tsocket"})) begin
            `uvm_info(get_type_name(),$sformatf("SV svtop::connect failed %s", local_env.prod.nb_initiator_socket.get_full_name()),UVM_LOW);
	    `uvm_fatal("MLCONN", "uvm_ml connect failed");
	 end;      
      end;
    
      if(e_active == TRUE) begin
	 if(!uvm_ml::connect({e_producer, "b_socket"}, {sv_consumer, "b_target_socket"})) begin
            `uvm_info(get_type_name(),$sformatf("SV svtop::connect failed %s", {e_producer, "b_socket"}),UVM_LOW);
	    `uvm_fatal("MLCONN", "uvm_ml connect failed");
	 end;
	 if(!uvm_ml::connect({e_producer, "nb_socket"}, {sv_consumer, "nb_target_socket"})) begin
            `uvm_info(get_type_name(),$sformatf("SV svtop::connect failed %s", {e_producer, "nb_socket"}),UVM_LOW);
	    `uvm_fatal("MLCONN", "uvm_ml connect failed");
	 end;
      end;      
    endfunction

    // Avoid premature termination
    task run_phase (uvm_phase phase);
      phase.raise_objection(this);
      #100;
      phase.drop_objection(this);
    endtask

    function void resolve_bindings();
      `uvm_info(get_type_name(),$sformatf("SV env::resolve_bindings %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void end_of_elaboration();
      `uvm_info(get_type_name(),$sformatf("SV env::end_of_elaboration %s", get_full_name()),UVM_LOW);
    endfunction

    function void start_of_simulation();
      `uvm_info(get_type_name(),$sformatf("SV env::start_of_simulation %s", get_full_name()),UVM_LOW);
    endfunction

    `uvm_component_utils(svtop)

  endclass

module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];   
   tops[0] = "";   
   uvm_ml_run_test(tops, "SV:svtop");
end
`endif
endmodule
