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

/*! \file ml_tlm2.h
  \brief TLM2 header file defining the TLM2 macros.
*/
#ifndef ML_TLM2_H
#define ML_TLM2_H

#include "systemc.h"  // Basic SystemC header file
#include "tlm.h"      // Basic SystemC TLM header file
#include "common/uvm_ml_adapter.h"
#include "common/ml_tlm2/ml_tlm2_internals.h"

using namespace tlm;

namespace uvm_ml {

// //////////////////////////////////////////////////////////
// Socket registration macros
// //////////////////////////////////////////////////////////

#define ML_TLM2_REGISTER_TARGET(module_i,tran_t,sckt,buswidth) \
  ml_tlm2_register_target <tran_t, buswidth> \
    (module_i, (module_i).sckt, #sckt, this->name());

#define ML_TLM2_REGISTER_TARGET_WITH_PROTOCOL(module_i,tran_t,sckt,buswidth,protocol_types) \
  ml_tlm2_register_target <tran_t, buswidth, protocol_types>	\
    (module_i, (module_i).sckt, #sckt, this->name())

#define ML_TLM2_REGISTER_INITIATOR(module_i,tran_t,sckt,buswidth) \
  ml_tlm2_register_initiator <tran_t, buswidth>		       \
    (module_i, (module_i).sckt, #sckt, this->name())

#define ML_TLM2_REGISTER_INITIATOR_WITH_PROTOCOL(module_i,tran_t,sckt,buswidth,protocol_types) \
  ml_tlm2_register_initiator <tran_t, buswidth, protocol_types>	\
    (module_i, (module_i).sckt, #sckt, this->name())

} // end namespace uvm_ml


///////////////////////////////////////////////////////////
//             THE COMMUNICATION MACROS                  //
///////////////////////////////////////////////////////////

#define ML_TLM2_GP_BEGIN(T) \
static gp_mm<T>* global_##T##_mm = gp_mm<T>::get();	\
class ml_tlm2_##T##_companion: public ml_tlm2_gp_companion { \
public: \
  ml_tlm2_##T##_companion():ml_tlm2_gp_companion(#T) { } \
  ~ml_tlm2_##T##_companion() {} \
  virtual void * create_class(const std::string& name = "") { \
    return global_##T##_mm->allocate();	\
  } \
  virtual void uvm_ml_automation(uvm_ml_packer * p, void * actual_arg, void* other_arg, ml_tlm2_oper op) { \
    T * actual UNUSED = (T*) actual_arg; \
    T * other UNUSED = (T*) other_arg;

#define ML_TLM2_GP_END(T) \
  } \
}; \
static bool ml_tlm2_##T##_dummy UNUSED = uvm_ml_class_company::register_class_companion(typeid(T), new ml_tlm2_##T##_companion());

#define ML_TLM2_GP_EXT_BEGIN(T) \
class ml_tlm2_##T##_companion: public ml_tlm2_ext_companion { \
public: \
  ml_tlm2_##T##_companion():ml_tlm2_ext_companion(#T) { } \
  ~ml_tlm2_##T##_companion() {} \
  virtual void * create_class(const std::string& name = "") { \
    return new T; \
  } \
  unsigned int get_ext_id(tlm_extension_base * ext) { \
    T * act = dynamic_cast<T *>(ext); \
    return act->ID; \
  } \
  virtual tlm_extension_base * get_other_ext(tlm_generic_payload * tlm_gp) {  \
    T * other_ext = NULL; \
    tlm_gp->get_extension(other_ext); \
    return other_ext; \
  } \
  virtual void uvm_ml_automation(uvm_ml_packer * p, void * actual_arg, void* other_arg, ml_tlm2_oper op) { \
    T * actual = (T*) actual_arg;      \
    T * other = (T*) other_arg;

#define ML_TLM2_GP_EXT_END(T)	\
  } \
}; \
static bool ml_tlm2_##T##_dummy UNUSED = uvm_ml_class_company::register_class_companion(typeid(T), new ml_tlm2_##T##_companion());

// Macro ML_TLM2_FIELD defines a fragment of ml_tlm2_automation for the 
// specific field
#define ML_TLM2_FIELD(f) \
  if (op == ML_TLM2_PACK_OP) \
    (*p) << actual->f;		    \
  else if (op == ML_TLM2_UNPACK_OP) \
    (*p) >> actual->f; \
  else if (op == ML_TLM2_BW_UPDATE_OP) \
    actual->f = other->f;
    
#define ML_TLM2_FIELD_DELETABLE(f) \
  if (op == ML_TLM2_PACK_OP) \
    (*p) << actual->f;		    \
  else if (op == ML_TLM2_UNPACK_OP) \
    (*p) >> actual->f;              \
  else if (op == ML_TLM2_DELETE_OP) { \
    if (actual->f) {				\
      delete actual->f; \
      actual->f = NULL; \
    } \
  } else if (op == ML_TLM2_BW_UPDATE_OP) {	\
    actual->f->copy(other->f);			\
  }

#define ML_TLM2_FIELD_ENUM(T,f)       \
  if (op == ML_TLM2_PACK_OP)          \
    (*p) << (int) actual->f;        \
  else if (op == ML_TLM2_UNPACK_OP) { \
    int tmp;                          \
    (*p) >> tmp;                      \
    actual->f = (T)tmp;             \
  }                                   \
  else if (op == ML_TLM2_BW_UPDATE_OP) \
    actual->f = other->f;

#define ML_TLM2_LOCAL(f) actual->f

#define ML_TLM2_FIELD_ARRAY(T,f,n) \
  if (op == ML_TLM2_PACK_OP) {     \
    (*p) << n;                     \
    for (int j = 0; j < n; j++)    \
      (*p) << actual->f[j];	   \
  } \
  else if (op == ML_TLM2_UNPACK_OP) { \
    T tmp;                            \
    int sz;                           \
    (*p) >> sz;                       \
    if (sz)                           \
      actual->f = new T[sz];          \
    for (int j = 0; j < sz; j++) {    \
      (*p) >> tmp;                    \
       actual->f[j] = tmp;            \
    }                                 \
  }				      \
  else if (op == ML_TLM2_DELETE_OP) { \
    if (n && (actual->f != NULL)) {   \
       delete [] actual->f;           \
       actual->f = NULL;	      \
    }				      \
  }                                   \
  else if (op == ML_TLM2_BW_UPDATE_OP) { \
    for (int j = 0; j < n; j++)    \
      actual->f[j] = other->f[j];  \
  } 

#define ML_TLM2_FIELD_ARRAY_ENUM(T,f,n) \
  if (op == ML_TLM2_PACK_OP) {     \
    (*p) << n;                     \
    for (int j = 0; j < n; j++)    \
      (*p) << (int) (actual->f[j]);\
  } \
  else if (op == ML_TLM2_UNPACK_OP) { \
    int tmp;                          \
    int sz;                           \
    (*p) >> sz;                       \
    if (sz)                           \
      actual->f = new T[sz];          \
    for (int j = 0; j < n; j++) {     \
       (*p) >> tmp;                   \
       actual->f[j] = (T) tmp;	      \
    }                                 \
  } \
  else if (op == ML_TLM2_BW_UPDATE_OP) { \
    for (int j = 0; j < n; j++)    \
      actual->f[j] = other->f[j];  \
  }  
                                 
#define ML_TLM2_FIELD_ACCESSORS(T, getr, setr) \
  if (op == ML_TLM2_PACK_OP) \
    (*p) << actual->getr(); \
  else if (op == ML_TLM2_UNPACK_OP) { \
    T t; \
    (*p) >> t; \
    actual->setr(t); \
    } \
  else if (op == ML_TLM2_BW_UPDATE_OP) \
    actual->setr(other->getr());

ML_TLM2_GP_BEGIN(tlm_generic_payload) \
ML_TLM2_GP_END(tlm_generic_payload)

#endif
