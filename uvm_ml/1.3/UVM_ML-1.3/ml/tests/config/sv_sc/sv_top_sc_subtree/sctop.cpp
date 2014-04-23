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
  int address;

  producer(sc_module_name nm) : uvm_component(nm), aport("aport") {
    cout << "SC producer::producer name= " << this->name() << endl;
    cout << "SC producer::aport " << aport.name() << endl;
  }

  UVM_COMPONENT_UTILS(producer)

  void run() {
    wait(50, SC_NS);
    for (int i = address; i < address+N; i++) {
      T pkt(i);
      cout << "[SC " << sc_time_stamp() << "] producer, writing on tlm_analysis_port: ";
      pkt.print(cout);
      aport.write(pkt);
      wait(10, SC_NS);
      cnt = i;
    }
    if(cnt == (address - 1) +N) 
      cout << "TEST PASSED" << endl;
    else
      cout << "TEST FAILED" << endl;
  }
  void build() { 
    cout << "SC producer::build " << this->name() << endl;
    get_config_int("address", address);
    cout << "SC producer:: address = "<< dec << address << endl;
    if (address != 0x1000 && address != 0 )
        SC_REPORT_ERROR("MLCFGERR", "Incorrect address value");
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
    aexport(*this);
    cout << "SC consumer::consumer name= " << this->name() << endl;
    cout << "SC consumer::aexport " << aexport.name() << endl;
  }
  void write(const T& t) {
    cout << "[SC " << sc_time_stamp() << "]" << " consumer::write: " << t;
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

// The environment component contains a producer and a consumer
class env : public uvm_component {
public:
  producer<packet> * prod;
  consumer<packet> * cons;

  env(sc_module_name nm) : uvm_component(nm)
			 , prod(NULL)
			 , cons(NULL)
  {
    cout << "SC env::env name= " << this->name() << endl;
  }
  void before_end_of_elaboration() {
    cout << "SC env::before_end_of_elaboration " << this->name() << endl;
  }
  void build() { 
    bool sc_active = false;
    int       intval = 0;
    short int sint   = 0;
    long long int  lint   = 0;
    int       byte   = 0;
    int       bit    = 0;

    unsigned       int uintval = 0;
    unsigned short int usint   = 0;
    unsigned long  long int ulint   = 0;
    unsigned int       ubyte   = 0;

    sc_bv_base bv(128);

    string   config_string;
    uvm_object *obj;
    packet *config_packet = NULL;

    cout << "SC env::build " << this->name() << endl;

    get_config_int("sc_active", sc_active);
    if (sc_active)
	    prod = new producer<packet>(sc_module_name("producer"));
    
    cons = new consumer<packet>("consumer");

    cout << "=====================================" << endl;
    cout << "----- CONFIG TESTING" << endl;
    cout << hex;

    get_config_int("int", intval);
    cout << "SC get_config: int = " << intval << endl; 
    if (intval != 0x7FFFFFFF)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect int value");

    get_config_int("shortint", sint);
    cout << "SC get_config: shortint = " << sint << endl; 
    if (sint != 0x7FFF)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect short int value");

    get_config_int("longint", lint);
    cout << "SC get_config: longint = " << lint << endl; 
    if (lint != 0x7FFFFFFFFFFFFFFFLL )
        SC_REPORT_ERROR("MLCFGERR", "Incorrect long int value");

    get_config_int("byte", byte);
    cout << "SC get_config: byte = " << byte << endl; 
    if (byte != 0x7F)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect byte value");

    get_config_int("bit", bit);
    cout << "SC get_config: bit = " << bit << endl; 
    if (bit != 0x1)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect bit value");

    get_config_int("uint", uintval);
    cout << "SC get_config: uint = " << uintval << endl; 
    if (uintval != 0xFFFFFFFF)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect unsigned int value");

    get_config_int("ushortint", usint);
    cout << "SC get_config: ushortint = " << usint << endl; 
    if (usint != 0xFFFF)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect unsigned short value");

    get_config_int("ulongint", ulint);
    cout << "SC get_config: ulongint = " << ulint << endl; 
    if (ulint != 0xFFFFFFFFFFFFFFFFLL)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect unsigned long value");

    get_config_int("ubyte", ubyte);
    cout << "SC get_config: ubyte = " << ubyte << endl; 
    if (ubyte != 0xFF)
        SC_REPORT_ERROR("MLCFGERR", "Incorrect unsigned byte value");

    get_config_int("bit128", bv);
    cout << "SC get_config: bit128 = " << bv << endl; 
    for (int i = 0; i < 4; i++)
    {
        if (bv.get_word(i) != 0xFFFFFFFF)
            SC_REPORT_ERROR("MLCFGERR", "Incorrect bit128 value");
    }

    get_config_object("config_packet", obj);
    if (obj != NULL)
    {
        config_packet = DCAST<packet*> (obj);
        cout << "SC get_config: object data = " << config_packet->data << endl;
    }
    else
    {
        SC_REPORT_ERROR("MLCFGERR", "Error getting config objecte");
    }

    get_config_string("config_string", config_string);
    cout << "SC get_config: config_string = " << config_string << endl; 
    if (config_string.compare("SV config test string") != 0)
      cout << "***Incorrect value for string" << endl;
    //to be fixed in 13.2
    //SC_REPORT_ERROR("MLCFGERR", "Incorrect string value");


    cout << "=====================================" << endl;

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

// Top level component registers ML ports
class sctop : public uvm_component
{
public:
  env * sc_env;

  sctop(sc_module_name nm) : uvm_component(nm)
  { 
    cout << "SC sctop::sctop name= " << this->name() << " type= " << this->get_type_name() << endl;
    //uvm_ml_register(&sc_env.prod->aport); 
    //uvm_ml_register(&sc_env.cons.aexport); 
  }
  void build() {
    cout << "SC sctop::build " << this->name() << endl;
    sc_env = new env("sc_env");
  }
  void before_end_of_elaboration() {
    cout << "SC sctop::before_end_of_elaboration " << this->name() << endl;
  }
  void connect() { 
    cout << "SC sctop::connect " << this->name() << endl;
    if (sc_env->prod != NULL)
        uvm_ml_register(&sc_env->prod->aport); 
    uvm_ml_register(&sc_env->cons->aexport); 
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
