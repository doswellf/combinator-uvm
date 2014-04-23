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
#include "producer.h"
#include "consumer.h"

using namespace tlm;
using namespace uvm_ml;

class sctop : public sc_module
{
public:
  consumer<packet> cons;
  producer<packet> prod;

  sctop(sc_module_name nm) : sc_module(nm) 
			   , cons("cons")
			   , prod("prod")
  {
      cout << "SC sctop::sctop" << endl;
  }
  void build() { 
    cout << "SC sctop::build" << endl;
  }
  void start_of_simulation() { 
    cout << "SC sctop::start_of_simulation" << endl;
  }

  void end_of_construction() { 
    cout << "SC sctop::end_of_construction" << endl;
  }
  void end_of_elaboration() { 
    cout << "SC sctop::end_of_elaboration" << endl;
  }

  void before_end_of_elaboration() {
    cout << "SC sctop::before_end_of_elaboration" << endl;
    uvm_ml_register(&prod.put_port);
    uvm_ml_register(&prod.get_port);
    uvm_ml_register(&prod.peek_port);
    uvm_ml_register(&prod.trans_port);
    uvm_ml_register(&prod.put_nb_port);
    uvm_ml_register(&prod.get_nb_port);
    uvm_ml_register(&prod.peek_nb_port);
    uvm_ml_register(&prod.a_port);
    uvm_ml_register(&cons.put_export);
    uvm_ml_register(&cons.get_export);
    uvm_ml_register(&cons.peek_export);
    uvm_ml_register(&cons.trans_export);
    uvm_ml_register(&cons.put_nb_export);
    uvm_ml_register(&cons.get_nb_export);
    uvm_ml_register(&cons.peek_nb_export);
    uvm_ml_register(&cons.a_export);
    uvm_ml_register(&prod.put_export);
  }
  void connect() { 
    cout << "SC sctop::connect" << endl;
  }
  void extract() { 
    cout << "SC sctop::extract" << endl;
  }
  void check() { 
    cout << "SC sctop::check" << endl;
  }
  void report() { 
    cout << "SC sctop::report" << endl;
  }
  void end_of_simulation() {
    cout << "SC sctop::end_of_simulation" << endl;
    sc_assert(cons.check_sum==6); 
  }
};

UVM_COMPONENT_REGISTER_T(producer, packet)
UVM_COMPONENT_REGISTER_T(consumer, packet)

#ifndef NC_SYSTEMC
int sc_main(int argc, char** argv) {
  return 0;
}
#endif

UVM_ML_MODULE_EXPORT(sctop)
