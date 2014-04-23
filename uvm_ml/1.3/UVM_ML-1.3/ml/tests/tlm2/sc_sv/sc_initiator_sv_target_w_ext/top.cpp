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

// Create generic payload transaction with extension
void top::create_trans(int base, PAYLOAD_TYPE* transact, tlm::tlm_command cmd) {
  cout<<"[SC "<<sc_time_stamp()<<"] creating transaction with base = "<<base<<endl;
  int i;
  unsigned char *data;
  data = new unsigned char[base+1];
  unsigned char byte_enable[base+1];
  transact->set_address(base*1000+base*100+base*10+base);
  transact->set_command(cmd);
  for (i=0; i<=base; i++){
    data[i] = i;
  };
  transact->set_data_ptr(&data[0]);
  transact->set_data_length(base+1);
  transact->set_response_status(tlm::TLM_OK_RESPONSE);
  for (i=base; i>=0; i--){
    byte_enable[i] = i;
  };
  transact->set_byte_enable_ptr(&byte_enable[0]);

  ext1 * ext = new ext1;

  ext->fill(base + 1);

  transact->set_auto_extension(ext);
}

void top::thread_process() {
  tlm_phase             phase = tlm::BEGIN_REQ;
  sc_time               time((sc_dt::uint64)5050, true);
  int ind;
  trans* tgp;
  sc_time my_t;
  sc_time* delay;

  delay = new sc_time(5000,SC_NS);
  tgp = mem_manager.allocate();
  tgp->acquire();
  ind = 0;
  cout<<"[SC "<<sc_time_stamp()<<"] staring SC thread process."<<endl;
  for (int j = 0; j < 10; j++) {
     create_trans(ind,tgp,tlm::TLM_WRITE_COMMAND);
     my_t = sc_time_stamp();
     
     cout<<"[SC "<<sc_time_stamp()<<"] Calling b_transport"<<endl;
     i.isocket->b_transport(*tgp,time);
     cout<<"[SC "<<sc_time_stamp()<<"] After b_transport"<<endl;
     sc_assert(sc_time_stamp() == my_t+*delay);
     wait(sc_time(1, SC_NS));
     ind++;
   };
   tgp->release();   
   cout<<"[SC] End of SC thread process"<<endl;
}

tlm::tlm_sync_enum initiator::nb_transport_bw( tlm_generic_payload& trans, tlm::tlm_phase& phase, sc_time& delay ) {
  cout << "[SC "<<sc_time_stamp()<<"] Starting nb_transport_bw of " << this->name() << endl;
  // implement response on bw path
  cout << "[SC "<<sc_time_stamp()<<"] End of nb_transport_bw of " << this->name() << endl;
  return tlm::TLM_ACCEPTED;
}

#ifndef NC_SYSTEMC
int sc_main(int argc, char** argv) {
    return 0;
}
#endif
UVM_ML_MODULE_EXPORT(top)
