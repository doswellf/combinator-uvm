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

#ifndef ML_TLM2_INTERNALS_H
#define ML_TLM2_INTERNALS_H

#include "systemc.h"          // Basic SystemC header file
#include "tlm.h"              // Basic SystemC TLM header file
#include "common/ml_tlm2/ml_tlm2_connector.h"

using namespace tlm;
using namespace uvm;

//////////////////

namespace uvm_ml {

std::string ml_tlm2_convertor_relative_name(const std::string &cur_context_name, 
                                            const std::string &containing_module_name, 
                                            const std::string &socket_name);
//////////////////

template <class REQ, unsigned int BUSWIDTH, typename TYPES> 
std::string ml_tlm2_register_target(const sc_module& containing_module, 
                                    tlm_target_socket<BUSWIDTH,TYPES> &s, 
                                    const std::string &target_socket_name,
                                    const std::string &cur_context_name)
{ 
  std::string target_socket_full_name = std::string(containing_module.name()) + "." + target_socket_name;
  //  assert ((new tlm1_to_tlm2<REQ, UVM_GP, BUSWIDTH, TYPES>(ml_tlm2_convertor_relative_name(cur_context_name,
  ml_tlm2_connector_base* conn = new ml_tlm2_target_connector<REQ, BUSWIDTH, TYPES>(
								   ml_tlm2_convertor_relative_name(cur_context_name,
								   containing_module.name(), 
								   target_socket_name).c_str(), 
								   s, target_socket_full_name);
  //assert(conn != NULL);
  if(conn == NULL) {
    char msg[1024];
    sprintf(msg, "\nModule name is '%s'; Target socket is '%s' \n", containing_module.name(), target_socket_name.c_str());
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: ml_tlm2_register_target failed because the connector could not be created",msg);
  };
  return target_socket_full_name;
}

//////////////////

template <class REQ, unsigned int BUSWIDTH, typename TYPES> 
std::string ml_tlm2_register_initiator(const sc_module& containing_module, 
                                       tlm_initiator_socket<BUSWIDTH,TYPES> &s, 
                                       const std::string &initiator_socket_name,
                                       const std::string &cur_context_name)
{ 
  std::string initiator_socket_full_name = std::string(containing_module.name()) + "." + initiator_socket_name;
  
  //  assert((new tlm2_to_tlm1<REQ, UVM_GP, BUSWIDTH, TYPES>(ml_tlm2_convertor_relative_name(cur_context_name,
  ml_tlm2_connector_base* conn = new ml_tlm2_initiator_connector<REQ, BUSWIDTH, TYPES>(
								 ml_tlm2_convertor_relative_name(cur_context_name,
								 containing_module.name(), 
								 initiator_socket_name).c_str(), 
								 s, initiator_socket_full_name);
  //assert(conn != NULL);
  if(conn == NULL) {
    char msg[1024];
    sprintf(msg, "\nModule name is '%s'; Target socket is '%s' \n", containing_module.name(), initiator_socket_name.c_str());
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: ml_tlm2_register_initiator failed because the connector could not be created",msg);
  };

  return initiator_socket_full_name;
}

//////////////////


template <class REQ, unsigned int BUSWIDTH, typename TYPES> 
std::string ml_tlm2_register_target(const sc_module& containing_module, 
                                    tlm_target_socket<BUSWIDTH,TYPES> *s, 
                                    const std::string &target_socket_name,
                                    const std::string &cur_context_name)
{
  return ml_tlm2_register_target<REQ,BUSWIDTH,TYPES>(containing_module, *s, target_socket_name, cur_context_name);
}

//////////////////

template <class REQ, unsigned int BUSWIDTH, typename TYPES> 
std::string ml_tlm2_register_initiator(const sc_module& containing_module, 
                                       tlm_initiator_socket<BUSWIDTH,TYPES> *s, 
                                       const std::string &initiator_socket_name,
                                       const std::string &cur_context_name)
{ 
  return ml_tlm2_register_initiator<REQ,BUSWIDTH,TYPES>(containing_module, *s, initiator_socket_name, cur_context_name);
}

//////////////////

class uvm_ml_class_companion: public uvm_creator {
private:
  string m_type_name;
public:
  uvm_ml_class_companion(const string & name);
  virtual ~uvm_ml_class_companion();

  const string & get_type_name() { return m_type_name; };
  virtual void   uvm_ml_automation(uvm_ml_packer * p, void * actual, void * other, ml_tlm2_oper op) = 0;
  virtual void   update(void * target, void * src) = 0;
};

//////////////////

class ml_tlm2_gp_companion: public uvm_ml_class_companion {
public:
  ml_tlm2_gp_companion(const string & name): uvm_ml_class_companion(name) {}
  virtual ~ml_tlm2_gp_companion();

  virtual void update(void * target, void * src);

  static void  clear(const type_info & actual_type, tlm_generic_payload * tlm_gp);

  static void  update_tlm_generic_payload(tlm_generic_payload * tlm_gp, tlm_generic_payload * other);

  static void  pack_tlm_generic_payload(uvm_ml_packer& p, tlm_generic_payload * tlm_gp);

  static void  unpack_tlm_generic_payload(uvm_ml_packer& p, tlm_generic_payload * tlm_gp);
};

//////////////////

class ml_tlm2_ext_companion: public uvm_ml_class_companion {
public:
  ml_tlm2_ext_companion(const string & name): uvm_ml_class_companion(name) {}
  virtual ~ml_tlm2_ext_companion();

  virtual void                 update(void * target, void * src);

  virtual unsigned int         get_ext_id(tlm_extension_base * ext) = 0;
  virtual tlm_extension_base * get_other_ext(tlm_generic_payload * tlm_gp) = 0;
};

//////////////////

typedef std::map<const type_info *, uvm_ml_class_companion *> uvm_ml_companion_map_type;

class uvm_ml_class_company: public uvm_factory {
private:
  static uvm_ml_companion_map_type * companion_map;
public:
  uvm_ml_class_company() {}
  virtual                         ~uvm_ml_class_company() {};
  static bool                     register_class_companion(const type_info & actual_type, uvm_ml_class_companion * c);
  static uvm_ml_class_companion * get_companion(const type_info & actual_type);

  static string                   get_type_name(const type_info & actual_type);
  static void                     update_class(const type_info & actual_type, void * target, void * src);

  static uvm_ml_companion_map_type & get_companion_map();
};

//////////////////

class ml_tlm2_class_company: public uvm_ml_class_company {
public:
  ml_tlm2_class_company() {}
  virtual ~ml_tlm2_class_company() {};

  static ml_tlm2_ext_companion   * get_ext_companion(const type_info & actual_type);
};
} // end namespace uvm_ml

//////////////////

template <typename GP_TYPE = tlm::tlm_generic_payload>
class gp_mm: public tlm::tlm_mm_interface
{

public:
  gp_mm() : free_list(0)
  {}

  GP_TYPE* allocate() {
    GP_TYPE* ptr;
    if (!free_list.empty()) {
      ptr = free_list.back();
      free_list.pop_back();      
    } else {
      ptr = new GP_TYPE();
      ptr->set_mm(this);
    }
    return ptr;
  }

  void free(tlm::tlm_generic_payload* trans) {
    ml_tlm2_gp_companion::clear(typeid(*trans), trans);
    free_list.push_back((GP_TYPE*)trans);
  }

  static gp_mm * get() {
    static gp_mm * m_mm = 0;
    if (!m_mm)
      m_mm = new gp_mm();
    return m_mm;
  }

private:
  std::vector<GP_TYPE*> free_list;
};

#ifdef __GNUC__
#define UNUSED __attribute__ ((unused))
#else
#define UNUSED
#endif

#endif // ML_TLM2_INTERNALS_H
