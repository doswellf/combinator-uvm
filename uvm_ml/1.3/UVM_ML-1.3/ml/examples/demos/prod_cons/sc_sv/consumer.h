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

template <class T>
class consumer : public uvm_component 
               , tlm_blocking_put_if<T> 
	       , tlm_nonblocking_put_if<T> 
               , tlm::tlm_fw_transport_if< tlm::tlm_base_protocol_types>
{
public:
  sc_export<tlm_blocking_put_if<T> > put_export;
  sc_export<tlm_nonblocking_put_if<T> > put_nb_export;
  tlm::tlm_target_socket <32, tlm::tlm_base_protocol_types> tsocket;
  int ind1, ind2;
  unsigned char* data;

  consumer(sc_module_name nm) : uvm_component(nm)
			      , put_export("put_export")
                              , put_nb_export("put_nb_export")
                              , tsocket("tsocket")
  { 
    tsocket(*this);
    put_export(*this);
    put_nb_export(*this);
  }

  UVM_COMPONENT_UTILS(consumer)

  void build() {
    cout << "SC consumer::build" << endl;
  }

  // methods to implement TLM1 put
  virtual void put( const T& t ) {
    cout << "[SC " <<  sc_time_stamp() << "] consumer::put: " << t << endl;
    save = t.data;
    wait(1, SC_NS);
    cout << "[SC " <<  sc_time_stamp() << "] consumer::put done " << endl;
  }

  virtual bool nb_put( const T& t ) {
    cout << "[SC " <<  sc_time_stamp() << "] consumer::nb_put: " << t << endl;
    save = t.data;
    return true;
  }

  virtual bool nb_can_put( tlm_tag<T> *t ) const {
    cout << "[SC " <<  sc_time_stamp() << "] consumer::nb_can_put" << endl;
    return true;
  }

  virtual const sc_event &ok_to_put( tlm_tag<T> *t ) const { 
    return dummy; 
  }

  // b_transport method for the TLM2 transactions
  void b_transport(PAYLOAD_TYPE& tx, sc_time& dt) {    
    tx.set_response_status(TLM_OK_RESPONSE);
    print_gp(tx);
    wait(10, SC_NS);
    ind1++;
  }

  // nb_transport method for the TLM2 transactions
  tlm::tlm_sync_enum nb_transport_fw(PAYLOAD_TYPE& trans,tlm::tlm_phase& phase, sc_time& delay ) {
    trans.acquire();  
    trans.set_response_status(TLM_OK_RESPONSE);
    print_gp(trans);
    ind2++;
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
    int i;
    unsigned char * data;
    
    data = gp.get_data_ptr();
    cout<<"[SC "<<sc_time_stamp()<<"] address = " << gp.get_address() << " data_length = "<<gp.get_data_length() << " m_data = ";
    
    for (i = 0; i<(int)gp.get_data_length(); i++){
      cout << hex << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }

  sc_event dummy;
  int save;
};
