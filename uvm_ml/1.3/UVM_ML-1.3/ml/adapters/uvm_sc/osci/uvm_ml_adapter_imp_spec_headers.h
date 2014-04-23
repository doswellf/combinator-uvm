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

/*! \file osci/uvm_ml_adapter_imp_spec_headers.h
  \brief OS specific variant of adapter code.
*/
#ifndef UVM_ML_ADAPTER_IMP_SPEC_HEADERS_H
#define UVM_ML_ADAPTER_IMP_SPEC_HEADERS_H
#include <map>
#include <queue>
#include <dlfcn.h>

#include "base/uvm_factory.h"
#include "base/uvm_packer.h"
#include "sysc/kernel/sc_simcontext.h"


#ifndef UVM_DEFINE_MESSAGE
#define UVM_DEFINE_MESSAGE(id, unused, text) \
 namespace sc_core { extern const char id[]; }
#endif


using namespace sc_core;

namespace sc_core {
enum uvm_ml_kernel_exception_message
{
  UVM_ML_QUASI_STATIC_ELABORATION,
  UVM_ML_CREATE_SC_INST,
  UVM_ML_CREATE_SC_INST_2
};

}

#endif
