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
#include "uvm_ml.h"
#include "ml_tlm2.h"
#include "packet.h"
#include "producer.h"
#include "consumer.h"

// Env containing a producer and a consumer
class env : public uvm_component {
public:
  producer<packet> prod;
  consumer<packet> cons;

  env(sc_module_name nm) : uvm_component(nm)
			 , prod("prod") 
			 , cons("cons")
  {
    cout << "SC env::env" << endl;
  }

  
  
  void before_end_of_elaboration() {
    cout << "SC env::before_end_of_elaboration" << endl;
    std::string full_initiator_nb_socket_name = 
      ML_TLM2_REGISTER_INITIATOR(prod, PAYLOAD_TYPE, nb_isocket , 32);
    std::string full_target_socket_name = 
      ML_TLM2_REGISTER_TARGET(cons, PAYLOAD_TYPE, tsocket, 32);
    std::string full_initiator_b_socket_name = 
      ML_TLM2_REGISTER_INITIATOR(prod, PAYLOAD_TYPE, b_isocket , 32);
    uvm_ml_connect(full_initiator_b_socket_name, 
		   "svtop.sv_env.consumer.b_target_socket");
  }
  UVM_COMPONENT_UTILS(env)
};

// Top level module
class sctop : public sc_module {
public:
  env sc_env;

  sctop(sc_module_name nm) : sc_module(nm) 
			   , sc_env("sc_env")
  {
    cout << "SC sctop::sctop" << endl;
  }

  void before_end_of_elaboration() {
    cout << "SC sctop::before_end_of_elaboration" << endl;
    uvm_ml_register(&sc_env.prod.put_port);
    uvm_ml_register(&sc_env.prod.put_nb_port);
    uvm_ml_register(&sc_env.cons.put_export);
    uvm_ml_register(&sc_env.cons.put_nb_export);
  }
  void end_of_elaboration() {
    cout << "SC sctop::end_of_elaboration" << endl;
  }
  void start_of_simulation() {
    cout << "SC sctop::start_of_simulation" << endl;
  }

};

#ifdef NC_SYSTEMC
NCSC_MODULE_EXPORT(sctop)
#else
int sc_main(int argc, char** argv) {
  return 0;
}
UVM_ML_MODULE_EXPORT(sctop)
#endif

UVM_COMPONENT_REGISTER_T(producer, packet)
UVM_COMPONENT_REGISTER_T(consumer, packet)
UVM_COMPONENT_REGISTER(env)
