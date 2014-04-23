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

// memory manager for TLM2 transactions
template <typename GP_TYPE = tlm::tlm_generic_payload>
class mm: public tlm::tlm_mm_interface
{

public:
  mm() : free_list(0)
  {}

  GP_TYPE* allocate() {
    GP_TYPE* ptr;
    if (!free_list.empty()) {
      ptr = free_list.back();
      free_list.pop_back();
    } else {
      ptr = new GP_TYPE(this);
    }
    return ptr;
  }

  void free(tlm::tlm_generic_payload* trans) {
    free_list.push_back((GP_TYPE*)trans);
  }

private:
  std::vector<GP_TYPE*> free_list;
};

template <typename T>
class producer : public uvm_component 
               , public tlm::tlm_bw_transport_if<tlm::tlm_base_protocol_types>
{
public:
  sc_port<tlm_blocking_put_if<T> > put_port;
  sc_port<tlm_nonblocking_put_if<T> > put_nb_port;
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> b_isocket;
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> nb_isocket;
  mm<PAYLOAD_TYPE> m_mm;
  int bw_count;
  producer(sc_module_name nm) : uvm_component(nm)
                              , put_port("put_port")
                              , put_nb_port("put_nb_port")
                              , b_isocket("b_isocket")
                              , nb_isocket("nb_isocket")
  { 
    nb_isocket(*this);
    b_isocket(*this);
    bw_count = 0;
  }
  UVM_COMPONENT_UTILS(producer)

  void build() {
    cout << "SC producer::build" << endl;
  }

  // main thread initiating TLM1 and TLM2 transactions
  void run() {
    T * t;
    T rsp;
    T req;
    bool ret;
    tlm_phase             phase = tlm::BEGIN_REQ;
    sc_time               time((sc_dt::uint64)10,true);
    tlm_sync_enum         status;
    int ind;
    tlm_generic_payload* tgp;
    sc_time ctime;
    sc_time* delay;
    mm<tlm_generic_payload>  mem_manager;
    
    delay = new sc_time(1,SC_NS);
    tgp = mem_manager.allocate();
    tgp->acquire();
    ind = 1;

    cout << "\nTLM2 non-blocking transactions from SC" << endl;

    create_trans(ind,tgp,tlm::TLM_WRITE_COMMAND);
    wait(sc_time(5, SC_NS));
    cout << "[SC " << sc_time_stamp() << "] producer::nb_transport_fw ";
    print_gp(*tgp);
    status = nb_isocket->nb_transport_fw(*tgp,phase,time);

    create_trans(ind,tgp,tlm::TLM_READ_COMMAND);
    wait(sc_time(5, SC_NS));
    phase = tlm::BEGIN_REQ;
    status = nb_isocket->nb_transport_fw(*tgp,phase,time);
    cout << "[SC " << sc_time_stamp() << "] producer::nb_transport_fw ";
    print_gp(*tgp);
    ind = ind+2;

    wait(10, SC_NS);
    cout << "\nTLM2 blocking transactions from SC" << endl;

    create_trans(ind,tgp,tlm::TLM_WRITE_COMMAND);
    cout << "[SC " << sc_time_stamp() << "] producer::b_transport sending";
    print_gp(*tgp);
    b_isocket->b_transport(*tgp, time);

    create_trans(ind,tgp,tlm::TLM_READ_COMMAND);
    b_isocket->b_transport(*tgp, time);
    cout << "[SC " << sc_time_stamp() << "] producer::b_transport received";
    print_gp(*tgp);
    ind = ind+2;
    
    tgp->release();   

    t = new T;
    wait(5, SC_NS);

    cout << "\nNonblocking TLM1 transactions from SC" << endl;
    for(int i = 0; i < 3; i++) {
      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::can_put " << endl;
      ret = put_nb_port->nb_can_put();
      cout << "[SC " << sc_time_stamp() << "] producer::can_put returned " << ret << endl;
      ind++;
      wait(5, SC_NS);
      t->data = 17+i;
      cout << "[SC " << sc_time_stamp() << "] producer::sending packet " << *t << endl;
      ret = put_nb_port->nb_put(*t);
      cout << "[SC " << sc_time_stamp() << "] producer::sent packet " << *t << endl;
      ind++;
      wait(5, SC_NS);
    }

    cout << "\nBlocking TLM1 transactions from SC" << endl;
    for (int j = 0; j < 3; j++) {
      t->data = 17+j;
      cout << "[SC " << sc_time_stamp() << "] producer::sending T " << *t << endl;
      put_port->put(*t);
      cout << "[SC " << sc_time_stamp() << "] producer::sent T " << *t << endl;
      wait(4, SC_NS);
    }
    wait(2, SC_NS);
    // VY    sc_assert(bw_count==3);
    sc_assert(bw_count==2);
  }

  // respond to backward path for TLM2 transactions
  tlm::tlm_sync_enum nb_transport_bw( PAYLOAD_TYPE& trans, tlm::tlm_phase& phase, sc_time& delay ) {
    cout << "[SC " << sc_time_stamp() <<"] nb_transport_bw " << endl;
    //print_gp(trans);
    bw_count++;
    return tlm::TLM_COMPLETED;
  }

  // must be implemented - but not important for ML stuff
  void invalidate_direct_mem_ptr(sc_dt::uint64 start_range, sc_dt::uint64 end_range){};

  // create generic payload for TLM2 transactions
  void create_trans(int base, PAYLOAD_TYPE* trans, tlm::tlm_command cmd) {
    cout<<"[SC " << sc_time_stamp() << "] creating transaction with base = "<<base<<endl;
    int i;
    unsigned char *data;

    data = new unsigned char[base+1];
    unsigned char byte_enable[base+1];
    trans->set_address(base*1000+base*100+base*10+base);
    trans->set_command(cmd);
    for (i=0; i<=base; i++){
      if(cmd == TLM_WRITE_COMMAND)
	data[i] = i;
      else
	data[i] = 0;
    };
    trans->set_data_ptr(&data[0]);
    trans->set_data_length(base+1);
    trans->set_response_status(tlm::TLM_INCOMPLETE_RESPONSE);
    for (i=base; i>=0; i--){
      byte_enable[i] = i;
    };
    trans->set_byte_enable_ptr(&byte_enable[0]);
    trans->set_byte_enable_length(0);  
  }  

  // print content of generic payload
  void print_gp(PAYLOAD_TYPE& gp){
    int i;
    unsigned char * data;
    
    data = gp.get_data_ptr();
    cout<<" address = " << hex << gp.get_address() << " data_length = "<<gp.get_data_length() << " m_data = ";
    
    for (i = 0; i<(int)gp.get_data_length(); i++){
      cout << hex << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }
};

