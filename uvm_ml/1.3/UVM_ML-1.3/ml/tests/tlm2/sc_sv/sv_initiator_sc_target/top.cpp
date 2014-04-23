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

void target::b_transport(PAYLOAD_TYPE& tx, sc_time& dt) {
  cout << "[SC "<<sc_time_stamp()<<"] Receiving b_transport of " << this->name() << endl;  
  print_gp(tx);
  wait(10, SC_PS);
  cout << "[SC "<<sc_time_stamp()<<"] Ending b_transport of " << this->name() << endl<<endl;
}


tlm::tlm_sync_enum target::nb_transport_fw(PAYLOAD_TYPE& trans,tlm::tlm_phase& phase, sc_time& delay ) 
{
  cout << "[SC "<<sc_time_stamp()<<"] Receiving nb_transport of " << this->name() << endl;
  trans.acquire();  
  print_gp(trans);
  sc_assert(check_data(trans,ind));
  cout << "[SC "<<sc_time_stamp()<<"] ending nb_transport of " << this->name() << endl;
  trans.release();
  ind++;

  return tlm::TLM_ACCEPTED;
}


void target::print_gp(PAYLOAD_TYPE& gp){
  int i;
  unsigned char * data;

  data = gp.get_data_ptr();
  cout<<"[SC "<<sc_time_stamp()<<"] data_length = "<<gp.get_data_length()<<endl;
  cout <<"[SC "<<sc_time_stamp()<<"] m_data = ";

  for (i = 0; i<(int)gp.get_data_length(); i++){
    cout << hex << (int)(*data++);
    cout<< " ";
  };
  cout<<endl;
}

bool target::check_data(PAYLOAD_TYPE& gp, int base){
  unsigned char * data;
  bool res;
  res = true;

  if(gp.get_data_length() != base){
    res = false;
  };
  if(gp.get_address() != base){
    res = false;
  };
  data = gp.get_data_ptr();
  for (int i = 0; i<(int)gp.get_data_length(); i++){
    if((int)(*data++) != base+i){
      res = false;
    };
  };
  if(gp.get_command()!=tlm::TLM_WRITE_COMMAND){
    res = false;
  };
  return res;
}
  
void top::thread_process() {
  wait(sc_time(2000, SC_PS));
  if(t.ind == 10) 
    cout << "** UVM TEST PASSED **" << endl;
  else
    cout << "** UVM TEST FAILED **" << endl;
  assert(t.ind == 10);
}

#ifndef NC_SYSTEMC
int sc_main(int argc, char** argv) {
  return 0;
}
#endif

UVM_ML_MODULE_EXPORT(top)
