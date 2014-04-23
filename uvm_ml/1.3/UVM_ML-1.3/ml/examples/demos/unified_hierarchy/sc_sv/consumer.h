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

// Consumer class responding to TLM2 transactions
class consumer : public uvm_component 
               , tlm::tlm_fw_transport_if< tlm::tlm_base_protocol_types>
{
public:
  tlm::tlm_target_socket <32, tlm::tlm_base_protocol_types> tsocket;

  consumer(sc_module_name nm) : uvm_component(nm)
                              , tsocket("tsocket")
  { 
    tsocket(*this);
  }

  UVM_COMPONENT_UTILS(consumer)

  void build() {
    cout << "SC consumer::build" << endl;
  }

  // blocking transport method for the TLM2 transactions
  void b_transport(tlm_generic_payload& tx, sc_time& dt) {    
    static char save_data[100];

    wait(dt.to_default_time_units(), SC_NS);
    tx.set_response_status(TLM_OK_RESPONSE);
    if(tx.get_command() == TLM_WRITE_COMMAND) {
      for(unsigned int i = 0; i < tx.get_data_length(); i++) {
	save_data[i] = *(tx.get_data_ptr()+i);
      };
    } else {
      for(unsigned int i = 0; i < tx.get_data_length(); i++) {
	*(tx.get_data_ptr()+i) = save_data[i];
      };
    };
    cout << "[SC " << sc_time_stamp() << "] consumer::b_transport";
    print_gp(tx);
  }

  // non-blocking transport method for the TLM2 transactions
  tlm::tlm_sync_enum nb_transport_fw(tlm_generic_payload& trans,tlm::tlm_phase& phase, sc_time& delay ) {
    static char save_data[100];

    trans.acquire();  
    trans.set_response_status(TLM_OK_RESPONSE);
    if(trans.get_command() == TLM_WRITE_COMMAND) {
      for(unsigned int i = 0; i < trans.get_data_length(); i++) {
	save_data[i] = *(trans.get_data_ptr()+i);
      };
    } else {
      for(unsigned int i = 0; i < trans.get_data_length(); i++) {
	*(trans.get_data_ptr()+i) = save_data[i];
      };
    };
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_transport ";
    print_gp(trans);
    trans.release();
    return tlm::TLM_COMPLETED;
  }

  // must be implemented for TLM2 - but not important for ML stuff
  virtual bool get_direct_mem_ptr(tlm_generic_payload& trans, tlm::tlm_dmi& dmi_data) {
    return false; 
  }

  // Not supported
  virtual unsigned int transport_dbg(tlm_generic_payload& trans) { 
    return 0; 
  }

  // print content of generic payload
  void print_gp(tlm_generic_payload& gp){
    int i;
    unsigned char * data;
    
    data = gp.get_data_ptr();
    if(gp.get_command() == TLM_READ_COMMAND) cout << " TLM_READ_COMMAND";
    if(gp.get_command() == TLM_WRITE_COMMAND) cout << " TLM_WRITE_COMMAND";
    cout<<" address = " << gp.get_address() << " data_length = "<<gp.get_data_length() << " m_data = ";
    
    for (i = 0; i<(int)gp.get_data_length(); i++){
      cout << hex << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }
};

UVM_COMPONENT_REGISTER(consumer)

