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
// e is the top component and it creates an SV subtree from its env

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
      `uvm_info(get_type_name(),"SV env::build",UVM_LOW);
      cons = consumer::type_id::create("consumer", this);
      prod = producer::type_id::create("producer", this);
    endfunction
   
    function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") begin
         uvm_ml::ml_tlm2#()::register(prod.b_initiator_socket);
         uvm_ml::ml_tlm2#()::register(prod.nb_initiator_socket);
         uvm_ml::ml_tlm2#()::register(cons.b_target_socket);
         uvm_ml::ml_tlm2#()::register(cons.nb_target_socket);
      end
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

module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];
   
   tops[0] = "";
   
   uvm_ml_run_test(tops, "e:top.e");
end
`endif
endmodule
