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
#define PROTOCOL_TYPES tlm_generic_protocol_types

class initiator: public sc_module, public tlm::tlm_bw_transport_if<tlm::tlm_base_protocol_types> {
public :
  mm<PAYLOAD_TYPE> m_mm;

  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> isocket;

  // constructor
  initiator(sc_module_name name_) : sc_module(name_),isocket("isocket") {
           isocket(*this);
  };
  tlm::tlm_sync_enum nb_transport_bw(PAYLOAD_TYPE& trans, tlm::tlm_phase& phase, sc_time& delay );    

  bool check_data(unsigned int base, PAYLOAD_TYPE* trans);
  // must be implemented - but not important for ML stuff
  void invalidate_direct_mem_ptr(sc_dt::uint64 start_range, sc_dt::uint64 end_range){};
};


class top : public sc_module {
public :
  initiator i;

  SC_HAS_PROCESS(top);

  // memory manager for generic payloads
  mm<tlm_generic_payload>  mem_manager;

  // constructor
  top(sc_module_name name_) : sc_module(name_),i("initiator") {
    
    cout << "SC :construction of " << this->name() << endl;
    std::string full_initiator_socket_name = ML_TLM2_REGISTER_INITIATOR(i, PAYLOAD_TYPE, isocket , 32);
    
    // run the main thread
    SC_THREAD(thread_process);
  }

  void thread_process();
  void create_trans(int base, PAYLOAD_TYPE* trans, tlm::tlm_command cmd);
};
