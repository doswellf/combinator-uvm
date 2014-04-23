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
  // SV interface
  sc_port<tlm_blocking_put_if<T> > put_port;
  sc_port<tlm_nonblocking_put_if<T> > put_nb_port;
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> b_isocket;
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> nb_isocket;
  // e interface
  sc_port<tlm_blocking_put_if<T> > sc_put_port;
  sc_port<tlm_nonblocking_put_if<T> > sc_put_nb_port;
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> sc_isocket;

  producer(sc_module_name nm) : uvm_component(nm)
                              , put_port("put_port")
                              , put_nb_port("put_nb_port")
                              , b_isocket("b_isocket")
                              , nb_isocket("nb_isocket")
                              , sc_put_port("sc_put_port")
                              , sc_put_nb_port("sc_put_nb_port")
                              , sc_isocket("sc_isocket")
    { 
      nb_isocket(*this);
      b_isocket(*this);
      sc_isocket(*this);
    }
  UVM_COMPONENT_UTILS(producer)

  void build() {
    cout << "SC producer::build" << endl;
  }

  // main thread initiating TLM1 and TLM2 transactions
  void run() {
    T * t;
    bool ret;
    int ind;
    tlm_phase               phase = tlm::BEGIN_REQ;
    sc_time                 delay((sc_dt::uint64)5,true);
    tlm_sync_enum           status;
    tlm_generic_payload*    tgp1;
    tlm_generic_payload*    tgp2;
    mm<tlm_generic_payload> mem_manager;

    tgp1 = mem_manager.allocate();
    tgp1->acquire();
    tgp2 = mem_manager.allocate();
    tgp2->acquire();
    ind = 1;

    wait(300, SC_NS);
    cout << "\n\n*** Starting non-blocking TLM2 transactions from SC to SV" << endl;

    create_trans(ind,tgp1,tlm::TLM_WRITE_COMMAND);
    cout << "[" << sc_time_stamp() << "] SC producer::nb_transport_fw sent";
    print_gp(*tgp1);
    status = nb_isocket->nb_transport_fw(*tgp1,phase,delay);
    wait(sc_time(5, SC_NS));

    create_trans(ind,tgp2,tlm::TLM_READ_COMMAND);
    status = nb_isocket->nb_transport_fw(*tgp2,phase,delay);
    wait(sc_time(5, SC_NS));
    cout << "[" << sc_time_stamp() << "] SC producer::nb_transport_fw received";
    print_gp(*tgp2);
    ind = ind+2;
    assert(*(tgp1->get_data_ptr()) == *(tgp2->get_data_ptr()));

    tgp1->release();   
    tgp2->release();   



    wait(10, SC_NS);
    cout << "\n\n*** Starting blocking TLM2 transactions from SC to SV" << endl;

    create_trans(ind,tgp1,tlm::TLM_WRITE_COMMAND);
    cout << "[" << sc_time_stamp() << "] SC producer::b_transport sent";
    print_gp(*tgp1);
    b_isocket->b_transport(*tgp1, delay);

    create_trans(ind,tgp2,tlm::TLM_READ_COMMAND);
    b_isocket->b_transport(*tgp2, delay);
    cout << "[" << sc_time_stamp() << "] SC producer::b_transport received";
    print_gp(*tgp2);
    ind = ind+2;
    assert(*(tgp1->get_data_ptr()) == *(tgp2->get_data_ptr()));
  

  
    t = new T;
    wait(5, SC_NS);
    cout << "\n\n*** Starting Non-blocking TLM1 transactions from SC to SV" << endl;
    for(int i = 0; i < 3; i++) {
      wait(5, SC_NS);
      cout << "[" << sc_time_stamp() << "] SC producer::can_put " << endl;
      ret = put_nb_port->nb_can_put();
      cout << "[" << sc_time_stamp() << "] SC producer::can_put returned " << ret << endl;
      wait(5, SC_NS);
      t->data = 17+i;
      cout << "[" << sc_time_stamp() << "] SC producer::sending packet " << *t << endl;
      ret = put_nb_port->nb_put(*t);
      cout << "[" << sc_time_stamp() << "] SC producer::sent packet " << *t << endl;
      wait(5, SC_NS);
    }



    wait(10, SC_NS);
    cout << "\n\n*** Starting Blocking TLM1 transactions from SC to SV" << endl;
    for (int j = 0; j < 3; j++) {
      t->data = 17+j;
      cout << "[" << sc_time_stamp() << "] SC producer::sending T " << *t << endl;
      put_port->put(*t);
      cout << "[" << sc_time_stamp() << "] SC producer::sent T " << *t << endl;
      wait(4, SC_NS);
    }



    tgp1->acquire();
    tgp2->acquire();

    wait(10, SC_NS);
    // This section is temporarily disabled
/*     cout << "\n\n*** Starting Blocking TLM2 transactions from SC to e" << endl; */
/*     create_trans(ind,tgp1,tlm::TLM_WRITE_COMMAND); */
/*     cout << "[" << sc_time_stamp() << "] SC producer::b_transport sent"; */
/*     print_gp(*tgp1); */
/*     sc_isocket->b_transport(*tgp1, delay); */

/*     create_trans(ind,tgp2,tlm::TLM_READ_COMMAND); */
/*     sc_isocket->b_transport(*tgp2, delay); */
/*     cout << "[" << sc_time_stamp() << "] SC producer::b_transport received"; */
/*     print_gp(*tgp2); */
/*     ind = ind+2; */
/*     assert(*(tgp1->get_data_ptr()) == *(tgp2->get_data_ptr())); */



    wait(10, SC_NS);
    cout << "\n\n*** Starting Non-blocking TLM2 transactions from SC to e" << endl;
    create_trans(ind,tgp1,tlm::TLM_WRITE_COMMAND);
    wait(sc_time(5, SC_NS));
    cout << "[" << sc_time_stamp() << "] SC producer::nb_transport_fw sent";
    print_gp(*tgp1);
    status = sc_isocket->nb_transport_fw(*tgp1,phase,delay);

    create_trans(ind,tgp2,tlm::TLM_READ_COMMAND);
    wait(sc_time(5, SC_NS));
    status = sc_isocket->nb_transport_fw(*tgp2,phase,delay);
    cout << "[" << sc_time_stamp() << "] SC producer::nb_transport_fw received";
    print_gp(*tgp2);
    ind = ind+2;
    assert(*(tgp1->get_data_ptr()) == *(tgp2->get_data_ptr()));

    tgp1->release();   
    tgp2->release();   



    wait(5, SC_NS);
    cout << "\n\n*** Starting Blocking TLM1 transactions from SC to e" << endl;
    for (int j = 0; j < 3; j++) {
      t->data = 17+j;
      cout << "[" << sc_time_stamp() << "] SC producer::sending T " << *t << endl;
      sc_put_port->put(*t);
      cout << "[" << sc_time_stamp() << "] SC producer::sent T " << *t << endl;
    }



    wait(5, SC_NS);
    cout << "\n\n*** Starting Non-blocking TLM1 transactions from SC to e" << endl;
    for(int i = 4; i < 7; i++) {
      cout << "[" << sc_time_stamp() << "] SC producer::can_put " << endl;
      ret = sc_put_nb_port->nb_can_put();
      cout << "[" << sc_time_stamp() << "] SC producer::can_put returned " << ret << endl;
      wait(5, SC_NS);
      t->data = 17+i;
      cout << "[" << sc_time_stamp() << "] SC producer::sending packet " << *t << endl;
      ret = sc_put_nb_port->nb_put(*t);
      cout << "[" << sc_time_stamp() << "] SC producer::sent packet " << *t << endl;
      wait(5, SC_NS);
    }

    wait(2, SC_NS);
  }

  // respond to backward path for TLM2 transactions
  tlm::tlm_sync_enum nb_transport_bw( PAYLOAD_TYPE& trans, tlm::tlm_phase& phase, sc_time& delay ) {
    //cout << "[SC " << sc_time_stamp() <<"] nb_transport_bw ";
    //print_gp(trans);
    return tlm::TLM_COMPLETED;
  }

  // must be implemented - but not important for ML stuff
  void invalidate_direct_mem_ptr(sc_dt::uint64 start_range, sc_dt::uint64 end_range){};

  // create generic payload for TLM2 transactions
  void create_trans(int base, PAYLOAD_TYPE* trans, tlm::tlm_command cmd) {
    int i;
    unsigned char *data;

    data = new unsigned char[base+1];
    unsigned char byte_enable[base+1];
    trans->set_address(base*1000+base*100+base*10+base);
    trans->set_command(cmd);
    for (i=0; i<=base; i++){
      if(cmd == TLM_WRITE_COMMAND)
	data[i] = rand() % 256;
      else
	data[i] = 0;
    };
    trans->set_data_ptr(&data[0]);
    trans->set_data_length(base+1);
    trans->set_response_status(tlm::TLM_INCOMPLETE_RESPONSE);
    for (i=base; i>=0; i--){
      byte_enable[i] = 0;
    };
    trans->set_byte_enable_ptr(&byte_enable[0]);
    trans->set_byte_enable_length(0);  
  }  

  // print content of generic payload
  void print_gp(PAYLOAD_TYPE& gp){
    unsigned char * data;
    
    data = gp.get_data_ptr();
    cout<<" address = " << dec << gp.get_address();
    cout << " data_length = "<<gp.get_data_length() << hex << " m_data = ";
    
    for (int i = 0; i<(int)gp.get_data_length(); i++){
      cout << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }
};

