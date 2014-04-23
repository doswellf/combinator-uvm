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
// e is the top component and it creates an SC subtree from its env

#include "uvm_ml.h"
using namespace uvm_ml;

#include "packet.h"

int N = getenv("N") ? atoi(getenv("N")) : 5;

// Template class of producer
// Produces 5 packets (17-21) and sends them through its ML analysis ports
template <typename T>
class producer: public uvm_component {
public:
  tlm_analysis_port<T> aport;
  int cnt;

  producer(sc_module_name nm) : uvm_component(nm), aport("aport") {
    cout << "SC producer::producer name= " << this->name() << endl;
    cout << "SC producer::aport " << aport.name() << endl;
  }
  UVM_COMPONENT_UTILS(producer)
  void run() {
    wait(50, SC_NS);
    for (int i = 17; i < 17+N; i++) {
      T pkt(i);
      cout << "[SC " << sc_time_stamp() << "] producer, writing on tlm_analysis_port: ";
      pkt.print(cout);
      aport.write(pkt);
      wait(10, SC_NS);
      cnt = i;
    }
    if(cnt == 16+N) 
      cout << "TEST PASSED" << endl;
    else
      cout << "TEST FAILED" << endl;
  }
  void build() { 
    cout << "SC producer::build " << this->name() << endl;
  }
  void before_end_of_elaboration() {
    cout << "SC producer::before_end_of_elaboration " << this->name() << endl;
  }
  void connect() { 
    cout << "SC producer::connect " << this->name() << endl;
  }
  void end_of_elaboration() { 
    cout << "SC producer::end_of_elaboration " << this->name() << endl;
  }
  void start_of_simulation() { 
    cout << "SC producer::start_of_simulation " << this->name() << endl;
  }
};

UVM_COMPONENT_REGISTER_T(producer, packet)

// Template class of consumer
// Prints the packets received through its export
template <typename T>
class consumer : public sc_module, public tlm_analysis_if<T> {
public:
  sc_export<tlm_analysis_if<T> > aexport;

  SC_CTOR(consumer) : aexport("aexport") {
  //consumer(sc_module_name nm) : uvm_component(nm), aexport("aexport") {
    aexport(*this);
    cout << "SC consumer::consumer name= " << this->name() << endl;
    cout << "SC consumer::aexport " << aexport.name() << endl;
  }
  void write(const T& t) {
    cout << "[SC " << sc_time_stamp() << "] " << name() << " consumer::write: " << t;
  }
  void before_end_of_elaboration() {
    cout << "SC consumer::before_end_of_elaboration " << this->name() << endl;
  }
  void build() { 
    cout << "SC consumer::build " << this->name() << endl;
  }
  void connect() { 
    cout << "SC consumer::connect " << this->name() << endl;
  }
  void end_of_elaboration() { 
    cout << "SC consumer::end_of_elaboration " << this->name() << endl;
  }
  void start_of_simulation() { 
    cout << "SC consumer::start_of_simulation " << this->name() << endl;
  }
};

// Top module contains a producer and a consumer
class env : public uvm_component {
public:
  producer<packet> prod;
  consumer<packet> cons;

  env(sc_module_name nm) : uvm_component(nm)
			 , prod(sc_module_name("producer")) 
			 , cons("consumer")
  {
    cout << "SC env::env name= " << this->name() << endl;
    uvm_ml_register(&prod.aport); 
    uvm_ml_register(&cons.aexport); 
  }
  void before_end_of_elaboration() {
    cout << "SC env::before_end_of_elaboration " << this->name() << endl;
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
    //uvm_ml_connect("sys.u.outport", sc_env.cons.aexport.name());
    //uvm_ml_connect(sc_env.prod.aport.name(), "sys.u.inport");
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

