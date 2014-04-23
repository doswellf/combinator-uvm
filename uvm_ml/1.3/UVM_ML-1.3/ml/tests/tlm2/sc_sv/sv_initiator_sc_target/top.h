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

#include "uvm_ml.h"
#include "ml_tlm2.h"

using namespace uvm;

// Memory management for tlm_generic_payload
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
      if(ptr->get_data_ptr() != NULL) delete ptr->get_data_ptr();
      ptr->set_data_ptr(NULL);
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

#define PAYLOAD_TYPE tlm_generic_payload

class target : public sc_module, tlm::tlm_fw_transport_if< tlm::tlm_base_protocol_types>{
public :
  unsigned char* data;
  int ind;
  tlm::tlm_target_socket <32, tlm::tlm_base_protocol_types> tsocket;

  // constructor
  target(sc_module_name name_) : sc_module(name_),tsocket("tsocket") {
    cout << "construction of " << this->name() << endl;
    tsocket(*this);
    ind = 0;
  }
  
  // destructor
  ~target() {};

  // b_transport method for the TLM2 transactions
  virtual void b_transport(PAYLOAD_TYPE& tx, sc_time& dt);

  //nb_transport method for the TLM2 transactions
  virtual tlm::tlm_sync_enum nb_transport_fw(PAYLOAD_TYPE& trans,
          tlm::tlm_phase& phase, sc_time& delay );

  // must be implemented - but not important for ML stuff
  virtual bool get_direct_mem_ptr(PAYLOAD_TYPE& trans, tlm::tlm_dmi& dmi_data) {
    return false; 
  }
  virtual unsigned int transport_dbg(PAYLOAD_TYPE& trans) { 
    return 0; 
  }
  virtual void print_gp(PAYLOAD_TYPE& gp);
  virtual bool check_data(PAYLOAD_TYPE& gp, int i);
};

class top : public sc_module {
public :
  target t; // simple tlm2 target

  SC_HAS_PROCESS(top);

  // memory manager for generic payloads
  mm<tlm_generic_payload>  mem_manager;

  // constructor
  top(sc_module_name name_) : sc_module(name_),t("t") {    
    cout << "SC :construction of " << this->name() << endl;

    std::string full_target_socket_name = ML_TLM2_REGISTER_TARGET(t, PAYLOAD_TYPE, tsocket, 32);

    cout << "SC: full_target_socket_name = " << full_target_socket_name << endl;
    
    // run the main thread
    SC_THREAD(thread_process);    
  }

  void thread_process();
};
