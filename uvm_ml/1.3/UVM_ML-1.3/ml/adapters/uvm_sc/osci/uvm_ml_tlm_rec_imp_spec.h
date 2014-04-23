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
/*! \file osci/uvm_ml_tlm_rec_imp_spec.h
  \brief OS specific definition of quasi static construction.
*/
#ifndef UVM_ML_TLM_REC_IMP_SPEC_H
#define UVM_ML_TLM_REC_IMP_SPEC_H
  static sc_module* quasi_static_construct_top(std::string name, std::string inst_name);
  static sc_module* create_sc_module_instance(std::string, std::string);

#endif
