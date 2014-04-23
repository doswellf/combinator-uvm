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

#include "top.h"

// Implement response to initiator
tlm::tlm_sync_enum initiator::nb_transport_bw( PAYLOAD_TYPE& trans, tlm::tlm_phase& phase, sc_time& delay ) {
  cout << "[SC "<<sc_time_stamp()<<"] Starting nb_transport_bw of " << this->name() << endl;
   sc_assert(check_data(trans_count,&trans)==true);
  trans_count++; 
  cout << "[SC "<<sc_time_stamp()<<"] End of nb_transport_bw of " << this->name() << endl;
  return tlm::TLM_ACCEPTED;
}

//check tlm_generic_payload
bool initiator::check_data(int base, PAYLOAD_TYPE* gp){
unsigned char * data;
  bool res;
  res = true;

  if(gp->get_data_length() != base+1){
    res = false;
  };
  if(gp->get_address() != base*1000+base*100+base*10+base){
    res = false;
  };
  data = gp->get_data_ptr();
  for (int i = 0; i<(int)gp->get_data_length(); i++){
    if((int)(*data++) != i){
      res = false;
    };
  };
  if(gp->get_command()!=tlm::TLM_WRITE_COMMAND){
    res = false;
  };
  return res;
}

// Create tlm_generic_payload transaction
void top::create_trans(int base, PAYLOAD_TYPE* trans, tlm::tlm_command cmd) {
  int i;
  unsigned char *data;
  unsigned char byte_enable[base+1];

  cout<<"[SC "<<sc_time_stamp()<<"] creating transaction with base = "<<base<<endl;
  data = new unsigned char[base+1];
  trans->set_address(base*1000+base*100+base*10+base);
  trans->set_command(cmd);
  for (i=0; i<=base; i++){
    data[i] = i;
  };
  trans->set_data_ptr(&data[0]);
  trans->set_data_length(base+1);
  trans->set_response_status(tlm::TLM_OK_RESPONSE);
  for (i=base; i>=0; i--){
    byte_enable[i] = i;
  };
  trans->set_byte_enable_ptr(&byte_enable[0]);
}

// Send 10 transactions through initiator socket
void top::thread_process() {
  tlm_phase             phase = tlm::BEGIN_REQ;
  sc_time               time((sc_dt::uint64)5050,true);
  tlm_sync_enum         status;
  int                   ind;
  tlm_generic_payload * tgp;

  tgp = mem_manager.allocate();
  tgp->acquire();
  ind = 0;
  cout<<"[SC "<<sc_time_stamp()<<"] staring SC thread process."<<endl;

  for (int j = 0; j < 10; j++) {
     create_trans(ind, tgp, tlm::TLM_WRITE_COMMAND);
     wait(sc_time(1, SC_NS));
     cout<<"[SC "<<sc_time_stamp()<<"] Calling nb_transport_fw with data size "<< tgp->get_data_length() << endl;
     status = i.isocket->nb_transport_fw(*tgp, phase, time);
     cout<<"[SC "<<sc_time_stamp()<<"] After nb_transport_fw status = "<<status<<endl;
     ind++;
   };
  sc_assert(i.trans_count==ind);
   tgp->release();   
   cout<<"[SC "<<sc_time_stamp()<<"] End of SC thread process"<<endl;
}


SC_MODULE(test1) {
    SC_CTOR(test1) {
        cout << "[SC " << sc_time_stamp() << "] Construction of test1" << endl;
    }
    void before_end_of_elaboration()
    {
        cout << "[SC " << sc_time_stamp() << "] Test1: before end of elaboration" << endl;
    }

    void end_of_elaboration()
    {
        cout << "[SC " << sc_time_stamp() << "] Test1: end of elaboration" << endl;
    }

    void start_of_simulation() 
    {
        cout << "[SC " << sc_time_stamp() << "] Test1: start of simulation" << endl;
    }

    void end_of_simulation() 
    {
        cout << "[SC " << sc_time_stamp() << "] Test1: end of simulation" << endl;
    }
};


static test1 v1("v1");

#ifndef NC_SYSTEMC


int sc_main(int argc, char** argv) {
    return 0;
}

#endif

extern "C" {
    int sc_start_helper()
    {
#ifndef NC_SYSTEMC
        // NCSC has its own synchronization mechanism
        sc_start(SC_ZERO_TIME);
#endif
        return 0;
    }

    int sc_stop_helper()
    {
#ifndef NC_SYSTEMC
        // NCSC has its own synchronization mechanism
        sc_stop();
#endif
        return 0;
    }
}

UVM_ML_MODULE_EXPORT(top);

