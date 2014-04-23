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
#include "packet.h"

// helper class to implement the e interfaces
template <class T>
class consumer_helper : public tlm_blocking_put_if<T>  
                      , public tlm_nonblocking_put_if<T> 
	              , public tlm::tlm_fw_transport_if< tlm::tlm_base_protocol_types>
{
public:
  virtual void put( const T& t ) {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::put: " << t << endl;
    save = t.data;
    wait(5, SC_NS);
    cout << "[" <<  sc_time_stamp() << "] SC consumer::put done " << endl;
  }

  virtual bool nb_put( const T& t ) {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_put: " << t << endl;
    save = t.data;
    return true;
  }

  virtual bool nb_can_put( tlm_tag<T> *t ) const {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_can_put" << endl;
    return true;
  }

  virtual const sc_event &ok_to_put( tlm_tag<T> *t ) const { 
    return dummy; 
  }


  // b_transport method for the TLM2 transactions
  void b_transport(PAYLOAD_TYPE& tx, sc_time& dt) { 
    static char save_data[100];   
    tx.set_response_status(TLM_OK_RESPONSE);
    if(tx.get_command() == TLM_WRITE_COMMAND) {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::b_transport WRITE ";
      for(unsigned int i = 0; i < tx.get_data_length(); i++) {
	save_data[i] = *(tx.get_data_ptr()+i);
      };
    } else {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::b_transport READ ";
      for(unsigned int i = 0; i < tx.get_data_length(); i++) {
	*(tx.get_data_ptr()+i) = save_data[i];
      };
    };
    print_gp(tx);
    wait(5, SC_NS);
    cout << "[" <<  sc_time_stamp() << "] SC consumer::b_transport done" << endl;
  }

  // nb_transport method for the TLM2 transactions
  tlm::tlm_sync_enum nb_transport_fw(PAYLOAD_TYPE& trans,tlm::tlm_phase& phase, sc_time& delay ) {
    static char save_data[100];   
    trans.acquire();  
    trans.set_response_status(TLM_OK_RESPONSE);
    if(trans.get_command() == TLM_WRITE_COMMAND) {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_transport WRITE ";
      for(unsigned int i = 0; i < trans.get_data_length(); i++) 
	save_data[i] = *(trans.get_data_ptr()+i);
    } else {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_transport READ ";
      for(unsigned int i = 0; i < trans.get_data_length(); i++) 
	*(trans.get_data_ptr()+i) = save_data[i];
    };
    print_gp(trans);
    trans.release();
    return tlm::TLM_COMPLETED;
  }

  // must be implemented for TLM2 - but not important for ML stuff
  virtual bool get_direct_mem_ptr(PAYLOAD_TYPE& trans, tlm::tlm_dmi& dmi_data) {
    return false; 
  }

  virtual unsigned int transport_dbg(PAYLOAD_TYPE& trans) { 
    return 0; 
  }

  // print content of generic payload
  void print_gp(PAYLOAD_TYPE& gp){
    unsigned char * data;
    
    data = gp.get_data_ptr();
    cout<< hex << " address = " << dec << gp.get_address();
    cout << " data_length = "<<gp.get_data_length() << hex << " m_data = ";
    
    for (int i = 0; i<(int)gp.get_data_length(); i++){
      cout << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }

  sc_event dummy;
  int save;
};

template <class T>
class consumer : public uvm_component 
               , tlm_blocking_put_if<T> 
	       , tlm_nonblocking_put_if<T> 
               , tlm_blocking_get_if<T> 
               , tlm_nonblocking_get_if<T> 
	       , tlm::tlm_fw_transport_if< tlm::tlm_base_protocol_types>
{
public:
  // SV interface
  sc_export<tlm_blocking_put_if<T> > put_export;
  sc_export<tlm_nonblocking_put_if<T> > put_nb_export;
  sc_export<tlm_blocking_get_if<T> > get_export;
  sc_export<tlm_nonblocking_get_if<T> > get_nb_export;
  tlm::tlm_target_socket <32, tlm::tlm_base_protocol_types> tsocket;
  // e interface
  consumer_helper<T> ch;
  sc_export<tlm_blocking_put_if<T> > put_e_export;
  sc_export<tlm_nonblocking_put_if<T> > put_nb_e_export;
  tlm::tlm_target_socket <32, tlm::tlm_base_protocol_types> t_e_socket;

  consumer(sc_module_name nm) : uvm_component(nm)
    , put_export("put_export")
    , put_nb_export("put_nb_export")
    , get_export("get_export")
    , get_nb_export("get_nb_export")
    , tsocket("tsocket")
    , put_e_export("put_e_export")
    , put_nb_e_export("put_nb_e_export")
    , t_e_socket("t_e_socket")
  { 
    tsocket(*this);
    put_export(*this);
    put_nb_export(*this);
    get_export(*this);
    get_nb_export(*this);
    put_e_export(ch);
    put_nb_e_export(ch);
    t_e_socket(ch);
  }

  UVM_COMPONENT_UTILS(consumer)

  void build() {
    cout << "SC consumer::build" << endl;
  }

  // methods to implement TLM1 get
  virtual T get(tlm_tag<T> *t) {
    T tt;
    static int ind=3;
    ind++;
    tt.data = ind*10;
    cout << "[" <<  sc_time_stamp() << "] SC consumer::get: " << tt << endl;
    wait(1, SC_NS);
    return tt;
  }

  virtual bool nb_get(T &t) {
    static int ind;
    ind++;
    t.data = ind*10;
    cout << "[" <<  sc_time_stamp() << "] SC consumer::try_get: " << t << endl;
    return true;
  }

  virtual bool nb_can_get(tlm_tag<T> *t) const {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::can_get: " << t << endl;
    return true;
  }

  virtual const sc_event &ok_to_get( tlm_tag<T> *t ) const { return dummy; }

  // methods to implement TLM1 put
  virtual void put( const T& t ) {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::put: " << t << endl;
    save = t.data;
    wait(5, SC_NS);
    cout << "[" <<  sc_time_stamp() << "] SC consumer::put done " << endl;
  }

  virtual bool nb_put( const T& t ) {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_put: " << t << endl;
    save = t.data;
    return true;
  }

  virtual bool nb_can_put( tlm_tag<T> *t ) const {
    cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_can_put" << endl;
    return true;
  }

  virtual const sc_event &ok_to_put( tlm_tag<T> *t ) const { 
    return dummy; 
  }

  // b_transport method for the TLM2 transactions
  void b_transport(PAYLOAD_TYPE& tx, sc_time& dt) {    
    static char save_data[100];   
    tx.set_response_status(TLM_OK_RESPONSE);
    if(tx.get_command() == TLM_WRITE_COMMAND) {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::b_transport WRITE ";
      for(unsigned int i = 0; i < tx.get_data_length(); i++) 
	save_data[i] = *(tx.get_data_ptr()+i);
    } else {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::b_transport READ ";
      for(unsigned int i = 0; i < tx.get_data_length(); i++) 
	*(tx.get_data_ptr()+i) = save_data[i];
    };
    print_gp(tx);
    wait(5, SC_NS);
  }

  // nb_transport method for the TLM2 transactions
  tlm::tlm_sync_enum nb_transport_fw(PAYLOAD_TYPE& trans,tlm::tlm_phase& phase, sc_time& delay ) {
    static char save_data[100];   
    trans.acquire();  
    trans.set_response_status(TLM_OK_RESPONSE);
    if(trans.get_command() == TLM_WRITE_COMMAND) {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_transport WRITE ";
      for(unsigned int i = 0; i < trans.get_data_length(); i++) 
	save_data[i] = *(trans.get_data_ptr()+i);
    } else {
      cout << "[" <<  sc_time_stamp() << "] SC consumer::nb_transport READ ";
      for(unsigned int i = 0; i < trans.get_data_length(); i++) 
	*(trans.get_data_ptr()+i) = save_data[i];
    };
    print_gp(trans);
    trans.release();
    return tlm::TLM_COMPLETED;
  }

  // must be implemented for TLM2 - but not important for ML stuff
  virtual bool get_direct_mem_ptr(PAYLOAD_TYPE& trans, tlm::tlm_dmi& dmi_data) {
    return false; 
  }

  virtual unsigned int transport_dbg(PAYLOAD_TYPE& trans) { 
    return 0; 
  }

  // print content of generic payload
  void print_gp(PAYLOAD_TYPE& gp){
    unsigned char * data;
    
    data = gp.get_data_ptr();
    cout<<hex<<" address = " << dec << gp.get_address();
    cout << " data_length = "<<gp.get_data_length() << hex << " m_data = ";
    
    for (int i = 0; i<(int)gp.get_data_length(); i++){
      cout << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }

  sc_event dummy;
  int save;
};
