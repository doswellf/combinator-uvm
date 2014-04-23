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
// SV is the top component and it creates this SC subtree from its env

#include "uvm_ml.h"
#include "ml_tlm2.h"
#include "producer.h"
#include "consumer.h"
using namespace uvm_ml;

// The environment component contains a producer and a consumer
class env : public uvm_component {
public:
  producer prod;
  consumer cons;

  env(sc_module_name nm) : uvm_component(nm)
			 , prod("prod") 
			 , cons("cons") 
  {
    cout << "SC env::env name= " << this->name() << endl;
  }
  void before_end_of_elaboration() {
    cout << "SC env::before_end_of_elaboration " << this->name() << endl;
    std::string full_initiator_b_socket_name = 
      ML_TLM2_REGISTER_INITIATOR(prod, tlm_generic_payload, b_isocket , 32);
    cout << "SC env registered " << full_initiator_b_socket_name << endl;
    std::string full_initiator_nb_socket_name = 
      ML_TLM2_REGISTER_INITIATOR(prod, tlm_generic_payload, nb_isocket , 32);
    cout << "SC env registered " << full_initiator_nb_socket_name << endl;
    std::string full_target_socket_name = 
      ML_TLM2_REGISTER_TARGET(cons, tlm_generic_payload, tsocket , 32);
    cout << "SC env registered " << full_target_socket_name << endl;
  }
  void build() { 
    cout << "SC env::build " << this->name() << endl;
  }
  void connect() { 
    cout << "SC env::connect " << this->name() << endl;
  }
  void end_of_elaboration() { 
    cout << "SC env::end_of_elaboration " << this->name() << endl;
  }
  void start_of_simulation() { 
    cout << "SC env::start_of_simulation " << this->name() << endl;
  }
  UVM_COMPONENT_UTILS(env)
};
UVM_COMPONENT_REGISTER(env)



// Top level component instantiates env
class sctop : public uvm_component
{
public:
  env sc_env;

  sctop(sc_module_name nm) : uvm_component(nm)
			   , sc_env("sc_env")
  { 
    cout << "SC sctop::sctop name= " << this->name() << " type= " << this->get_type_name() << endl;
  }
  void build() {
    cout << "SC sctop::build " << this->name() << endl;
  }
  void before_end_of_elaboration() {
    cout << "SC sctop::before_end_of_elaboration " << this->name() << endl;
  }
  void connect() { 
    cout << "SC sctop::connect " << this->name() << endl;
  }
  void start_of_simulation() { 
    cout << "SC sctop::start_of_simulation " << this->name() << endl;
  }
  void end_of_elaboration() { 
    cout << "SC sctop::end_of_elaboration " << this->name() << endl;
  }
  UVM_COMPONENT_UTILS(sctop)
};

UVM_COMPONENT_REGISTER(sctop)



#ifdef NC_SYSTEMC
NCSC_MODULE_EXPORT(sctop)
#else
int sc_main(int argc, char** argv) {
  return 0;
}
UVM_ML_MODULE_EXPORT(sctop)
#endif
