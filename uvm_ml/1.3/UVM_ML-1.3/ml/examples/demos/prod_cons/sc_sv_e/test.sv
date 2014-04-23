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

`include "packet.sv"
`include "producer.sv"
`include "consumer.sv"

//----------------------------------------------------------------------
// env class
//----------------------------------------------------------------------
class env extends uvm_component;

    `uvm_component_utils(env)

    producer_1 prod1;   
    producer_2 prod2;
    consumer_1 cons1;
    consumer_2 cons2;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        `uvm_info(get_type_name(),"SV env::new ",UVM_LOW);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV env::build",UVM_LOW);
      prod1 = producer_1::type_id::create("producer_1", this);
      prod2 = producer_2::type_id::create("producer_2", this);
      cons1 = consumer_1::type_id::create("consumer_1", this);
      cons2 = consumer_2::type_id::create("consumer_2", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info(get_type_name(),"Connecting the sockets",UVM_LOW);
    endfunction

endclass

//----------------------------------------------------------------------
// top of SV tree
//----------------------------------------------------------------------
class svtest extends uvm_test;

    `uvm_component_utils(svtest)

    env sv_env;
    string e_producer = "sys.env.producer.";
    string e_consumer = "sys.env.consumer.";
    string sc_producer = "sctop.sc_env.prod.";
    string sc_consumer = "sctop.sc_env.cons.";

    function new(string name, uvm_component parent=null);
        super.new(name, parent);
        `uvm_info(get_type_name(),"SV svtest::new ",UVM_LOW);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(),"SV svtest::build ",UVM_LOW);
        sv_env = env::type_id::create("sv_env", this);
    endfunction

    // Register SV ML ports and sockets
    function void phase_ended(uvm_phase phase);
        if (phase.get_name() == "build") begin
	   // producer_1 ports
	   uvm_ml::ml_tlm2 #()::register(sv_env.prod1.b_initiator_socket);
	   uvm_ml::ml_tlm2 #()::register(sv_env.prod1.nb_initiator_socket);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.prod1.b_put_port);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.prod1.nb_put_port);
	   // producer_2 ports
	   uvm_ml::ml_tlm2 #()::register(sv_env.prod2.b_initiator_socket);
	   uvm_ml::ml_tlm2 #()::register(sv_env.prod2.nb_initiator_socket);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.prod2.b_put_port);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.prod2.nb_put_port);
	   // consumer_1 ports
           uvm_ml::ml_tlm2 #()::register(sv_env.cons1.nb_target_socket);
           uvm_ml::ml_tlm2 #()::register(sv_env.cons1.b_target_socket);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.cons1.put_export);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.cons1.put_nb_export);
	   // consumer_2 ports
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.cons2.put_export);
	   uvm_ml::ml_tlm1 #(packet)::register(sv_env.cons2.put_nb_export);
	   uvm_ml::ml_tlm2 #()::register(sv_env.cons2.b_target_socket);
	   uvm_ml::ml_tlm2 #()::register(sv_env.cons2.nb_target_socket);
         end
    endfunction

    // Bind ML connections
    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),"SV svtest::connect ",UVM_LOW);
      
      // e to SC connections
      if(!uvm_ml::connect({e_producer,  "sc_socket"}, 
			  {sc_consumer, "t_e_socket"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({e_producer,  "put_port"}, 
			  {sc_consumer, "put_e_export"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({e_producer,  "nb_put_port"}, 
			  {sc_consumer, "put_nb_e_export"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      // SC to e connections
      if(!uvm_ml::connect({sc_producer, "sc_put_port"}, 
			  {e_consumer,  "b_sc_put_in_port"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({sc_producer, "sc_put_nb_port"}, 
			  {e_consumer,  "nb_sc_put_in_port"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({sc_producer, "sc_isocket"}, 
			  {e_consumer,  "b_sc_tsocket"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      // e to SV connections
      if(!uvm_ml::connect({e_producer, "nb_socket"}, 
			  sv_env.cons1.nb_target_socket.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({e_producer, "b_socket"}, 
			  sv_env.cons1.b_target_socket.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({e_producer, "sv_put_port"},
			  sv_env.cons1.put_export.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({e_producer, "sv_nb_put_port"},
			  sv_env.cons1.put_nb_export.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      
      // SV to e connections
      if(!uvm_ml::connect(sv_env.prod1.b_initiator_socket.get_full_name(), 
			  {e_consumer, "b_tsocket"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod1.nb_initiator_socket.get_full_name(), 
			  {e_consumer, "nb_tsocket"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod1.b_put_port.get_full_name(), 
			  {e_consumer, "b_put_in_port"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod1.nb_put_port.get_full_name(), 
			  {e_consumer, "nb_put_in_port"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      
      // SV to SC connections
      if(!uvm_ml::connect(sv_env.prod2.b_initiator_socket.get_full_name(), 
			  {sc_consumer, "tsocket"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod2.nb_initiator_socket.get_full_name(), 
			  {sc_consumer, "tsocket"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod2.b_put_port.get_full_name(), 
			  {sc_consumer, "put_export"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect(sv_env.prod2.nb_put_port.get_full_name(), 
			  {sc_consumer, "put_nb_export"})) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      
      // SC to SV connections
      if(!uvm_ml::connect({sc_producer, "put_port"},
			  sv_env.cons2.put_export.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({sc_producer, "put_nb_port"},
			  sv_env.cons2.put_nb_export.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({sc_producer, "b_isocket"},
			  sv_env.cons2.b_target_socket.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
      if(!uvm_ml::connect({sc_producer, "nb_isocket"},
			  sv_env.cons2.nb_target_socket.get_full_name())) begin
	 `uvm_fatal("MLCONN", "uvm_ml connect failed");
      end;
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        for (integer i = 0; i < 600; i++) begin
            uvm_ml::synchronize();
            #1;
        end    
        phase.drop_objection(this);
    endtask
endclass

module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[2];

   tops[0] = "SC:sctop";
   tops[1] = "e:top.e";

   uvm_ml_run_test(tops, "sv:svtest");
end // initial begin
`endif
endmodule