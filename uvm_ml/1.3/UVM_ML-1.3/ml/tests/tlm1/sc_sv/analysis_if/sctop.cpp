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

#include "uvm_ml.h"
using namespace tlm;
using namespace uvm_ml;
using namespace uvm;

#include "packet.h"

int N = getenv("N") ? atoi(getenv("N")) : 5;


// Template class of producer
// Produces 5 packets (17-21) and sends them through its ML analysis ports
// Two ports demonstrate different ways to define the port

template <typename T>
SC_MODULE(producer) {
  tlm_analysis_port<T> aport;
  sc_port<tlm_analysis_if<T>, 2, SC_ONE_OR_MORE_BOUND > aport1;
  int cnt;

  SC_CTOR(producer) : aport("aport"), aport1("aport1") {
    SC_THREAD(run); 
  }

  void run() {
    for (int i = 17; i < 17+N; i++) {
      T pkt(i);
      cout << "[SC " << sc_time_stamp() << "] producer, writing on tlm_analysis_port: ";
      pkt.print(cout);
      aport.write(pkt);

      cout << "[SC " << sc_time_stamp() << "] producer, writing on sc_port<tlm_analysis_if> ";
      pkt.print(cout);
      for (int j = 0; j < aport1.size(); j++) {
        aport1[j]->write(pkt);
      }
      wait(10, SC_NS);
      cnt = i;
    }

    sc_assert(cnt == 16+N);
    if(cnt == 16+N) 
      cout << "** UVM TEST PASSED **" << endl;
    else
      cout << "** UVM TEST FAILED **" << endl;
  }
};

// Template class of subscriber
// Prints the packets received through its export

template <typename T>
class subscriber : public sc_module, public tlm_analysis_if<T> {
public:
  sc_export<tlm_analysis_if<T> > aexport;
  int expected_sc;
  bool flag;
  
  SC_CTOR(subscriber) : aexport("aexport") {
    aexport(*this);
    expected_sc = 17;
    flag = 0;
  }

  void write(const T& t) {
    cout << "[SC " << sc_time_stamp() << "] " << name() << " subscriber::write: " << t;

    sc_assert(t.kind == 0);
    sc_assert(expected_sc == t.data);
    if (flag == 1)
      expected_sc++;
    flag = !flag;
  };
};


// Top module contains a producer and a subscriber
// Registers the ports of the producer as ML
// The ports are bound in the SV code to 2 instances of subscriber

SC_MODULE(sctop) {
  producer<packet> prod;
  subscriber<packet> sub;
 
  SC_CTOR(sctop) : prod("producer"), sub("subscriber") {
    prod.aport(sub.aexport);
    prod.aport1(sub.aexport);
    uvm_ml_register(&prod.aport); 
    uvm_ml_register(&prod.aport1); 
  }
};

#ifndef NC_SYSTEMC
int sc_main(int argc, char** argv) {
  return 0;
}
#endif

UVM_ML_MODULE_EXPORT(sctop)
