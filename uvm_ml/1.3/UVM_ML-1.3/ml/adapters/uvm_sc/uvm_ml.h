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

/*! \file uvm_ml.h
  \brief Definition of macros and templates used by UVM-ML.
*/
#ifndef UVM_ML_H
#define UVM_ML_H

#include <vector>


#include "uvm.h"
#include "tlm.h"
#include "common/uvm_ml_packer.h"
#include "common/uvm_ml_adapter.h"
#ifdef NC_SYSTEMC
#include "sysc/cosim/sc_cosim_ids.h"
#include "sysc/cosim/ml_uvm_ids.h"
#endif

namespace uvm_ml {
#define uvm_ml_tlm_declare_register_funcs(IF) \
template <typename T, int N, sc_core::sc_port_policy POL> \
void uvm_ml_register( \
  sc_core::sc_port<tlm::IF<T>,N,POL>* p \
) { \
  uvm_ml_register_internal(p); \
} \
\
template <typename T> \
void uvm_ml_register( \
  sc_core::sc_export<tlm::IF<T> >* p \
) { \
  uvm_ml_register_internal(p); \
}

uvm_ml_tlm_declare_register_funcs(tlm_blocking_put_if)
uvm_ml_tlm_declare_register_funcs(tlm_nonblocking_put_if)
uvm_ml_tlm_declare_register_funcs(tlm_put_if)

uvm_ml_tlm_declare_register_funcs(tlm_blocking_get_if)
uvm_ml_tlm_declare_register_funcs(tlm_nonblocking_get_if)
uvm_ml_tlm_declare_register_funcs(tlm_get_if)

uvm_ml_tlm_declare_register_funcs(tlm_blocking_peek_if)
uvm_ml_tlm_declare_register_funcs(tlm_nonblocking_peek_if)
uvm_ml_tlm_declare_register_funcs(tlm_peek_if)

uvm_ml_tlm_declare_register_funcs(tlm_blocking_get_peek_if)
uvm_ml_tlm_declare_register_funcs(tlm_nonblocking_get_peek_if)
uvm_ml_tlm_declare_register_funcs(tlm_get_peek_if)

#if !defined(NC_SYSTEMC) || defined(__TLM_ANALYSIS_H__)

template <typename T, int N, sc_core::sc_port_policy POL> 
void uvm_ml_register( 
  sc_core::sc_port<tlm::tlm_analysis_if<T>,N,POL>* p 
) { 
  uvm_ml_register_internal(p);
} 

template <typename T> 
void uvm_ml_register( 
  tlm::tlm_analysis_port<T>* p 
) { 
  uvm_ml_register_internal(p);
} 

template <typename T> 
void uvm_ml_register( 
  sc_core::sc_export<tlm::tlm_analysis_if<T> >* p 
) { 
  uvm_ml_register_internal(p);
}
#endif

//////////////

template <typename REQ, typename RSP, int N, sc_core::sc_port_policy POL> 
void uvm_ml_register( 
  sc_core::sc_port<tlm::tlm_transport_if<REQ,RSP>,N,POL>* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;
  std::string s = std::string(p->basename()) + "_trans"; 
  uvm_ml_tlm_transmitter_tlm_transport<REQ,RSP>* trans = 
    new uvm_ml_tlm_transmitter_tlm_transport<REQ,RSP>(s.c_str()); 
  p->bind(*trans); 
  trans->object(p); 
  trans->set_intf_name("tlm_transport_if");
  trans->set_REQ_name(REQ().get_type_name());
  trans->set_RSP_name(RSP().get_type_name());
} 

template <typename REQ, typename RSP> 
void uvm_ml_register( 
  sc_core::sc_export<tlm::tlm_transport_if<REQ,RSP> >* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;
  std::string s = std::string(p->basename()) + "_rec"; 
  uvm_ml_tlm_receiver_tlm<REQ,RSP>* rec =  
    new uvm_ml_tlm_receiver_tlm<REQ,RSP>(s.c_str()); 
  rec->bind_export(p); 
  rec->set_intf_name("tlm_transport_if");
  rec->set_REQ_name(REQ().get_type_name());
  rec->set_RSP_name(RSP().get_type_name());
}

//////////////

template <typename REQ, typename RSP, int N, sc_core::sc_port_policy POL> 
void uvm_ml_register( 
  sc_core::sc_port<tlm::tlm_master_if<REQ,RSP>,N,POL>* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;
  std::string s = std::string(p->basename()) + "_trans"; 
  uvm_ml_tlm_transmitter_tlm<REQ,RSP>* trans = 
    new uvm_ml_tlm_transmitter_tlm<REQ,RSP>(s.c_str()); 
  p->bind(*trans); 
  trans->object(p); 
  trans->set_intf_name("tlm_master_if");
  trans->set_REQ_name(REQ().get_type_name());
  trans->set_RSP_name(RSP().get_type_name());
} 

template <typename REQ, typename RSP> 
void uvm_ml_register( 
  sc_core::sc_export<tlm::tlm_master_if<REQ,RSP> >* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;
  std::string s = std::string(p->basename()) + "_rec"; 
  uvm_ml_tlm_receiver_tlm<REQ,RSP>* rec =  
    new uvm_ml_tlm_receiver_tlm<REQ,RSP>(s.c_str()); 
  rec->bind_export(p); 
  rec->set_intf_name("tlm_master_if");
  rec->set_REQ_name(REQ().get_type_name());
  rec->set_RSP_name(RSP().get_type_name());
}

//////////////

template <typename REQ, typename RSP, int N, sc_core::sc_port_policy POL> 
void uvm_ml_register( 
  sc_core::sc_port<tlm::tlm_slave_if<REQ,RSP>,N,POL>* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;
  std::string s = std::string(p->basename()) + "_trans"; 
  // slave_if is templated by <REQ,RSP>, and it does put(RSP&) and
  // get(REQ&). A transmitter always does put(T1) and get(T2), so 
  // we need to instantiate transmitter templated by <RSP,REQ>
  uvm_ml_tlm_transmitter_tlm<RSP,REQ>* trans = 
    new uvm_ml_tlm_transmitter_tlm<RSP,REQ>(s.c_str()); 
  p->bind(*trans); 
  trans->object(p); 
  trans->set_intf_name("tlm_slave_if");
  // REQ_name and RSP_name are set according to the sc_port argument order
  // which is <REQ,RSP> because we will check compatibility of 
  // sc_port<tlm_slave_if<REQ,RSP> > with uvm_slave_imp#(REQ,RSP), and
  // that should match
  trans->set_REQ_name(REQ().get_type_name());
  trans->set_RSP_name(RSP().get_type_name());
} 

template <typename REQ, typename RSP> 
void uvm_ml_register( 
  sc_core::sc_export<tlm::tlm_slave_if<REQ,RSP> >* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;
  std::string s = std::string(p->basename()) + "_rec"; 
  // slave_if is templated by <REQ,RSP>, and it does put(RSP&) and
  // get(REQ&). A receiver always does put(T1) and get(T2), so 
  // we need to instantiate receiver templated by <RSP,REQ>
  uvm_ml_tlm_receiver_tlm<RSP,REQ>* rec =  
    new uvm_ml_tlm_receiver_tlm<RSP,REQ>(s.c_str()); 
  rec->bind_export(p); 
  // REQ_name and RSP_name are set according to the sc_port argument order
  // which is <REQ,RSP> because we will check compatibility of 
  // sc_export<tlm_slave_if<REQ,RSP> > with uvm_slave_port#(REQ,RSP), and that
  // should match
  rec->set_intf_name("tlm_slave_if");
  rec->set_REQ_name(REQ().get_type_name());
  rec->set_RSP_name(RSP().get_type_name());
}

// debugging aid: print_uvm works for both int* and uvm_object*
// find some better way to do this


template <class T> void print_uvm(std::ostream& os, T* val, void* t) {
  std::cerr << "print_uvm<T*>" << std::endl;
  os << *val << std::endl;
}

template <class T> void print_uvm(std::ostream& os, const T* val, const void* t) {
  std::cerr << "print_uvm<T*>" << std::endl;
  os << *val << std::endl;
}

template <class T> void print_uvm(std::ostream& os, T* val, uvm::uvm_object* t) {
  std::cerr << "print_uvm<uvm_object*>" << std::endl;
  val->print(os);
}

template <class T> void print_uvm(std::ostream& os, const T* val, const uvm::uvm_object* t) {
  std::cerr << "print_uvm<const uvm_object*>" << std::endl;
  val->print(os);
}

////////////////////////////
/// \param tops - a vector of UVM-ML tops
/// \param test - a pointer to a UVM-ML test
/// \note Run duration-wise, behaves similarly to sc_start().
void uvm_ml_run_test(const std::vector<std::string>& tops,  const char * test);
/// \param tops - a vector of UVM-ML tops
/// \param test - a pointer to a UVM-ML test
/// \param duration - run duration, similarly to sc_start(sc_time&)
void uvm_ml_run_test(const std::vector<std::string>& tops, const char * test, const sc_time & duration);
} // namespace uvm_ml

#ifndef NC_SYSTEMC
#define UVM_ML_MODULE_EXPORT(w) \
::sc_core::sc_module* F_##w(const char* name) { return new w(name); } \
static int dummy_##w = associate_module(#w, F_##w);
#else
#define UVM_ML_MODULE_EXPORT(w) NCSC_MODULE_EXPORT(w)
#endif

#endif
