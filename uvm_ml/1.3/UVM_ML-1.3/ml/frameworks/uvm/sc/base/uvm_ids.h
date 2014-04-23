//----------------------------------------------------------------------
//   Copyright 2009 Cadence Design Systems, Inc.
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

/*! \file uvm_ids.h
  \brief UVM SystemC kernel message IDs.
*/
#ifndef UVM_IDS_H
#define UVM_IDS_H

#include "sysc/utils/sc_report.h"


//-----------------------------------------------------------------------------
// Report ids (uvm) following the style of SystemC kernel message reporting.
//
// Report ids in the range of 1-100.

// If SystemC kernel is modified to be aware of the UVM message ids,
// then sysc/utils/sc_utils_ids.cpp has to include this file, and 
// has to define UVM_DEFINE_MESSAGE suitably with an offset added 
// to the message id such that the id does not clash with any id 
// already used by the SystemC kernel.  
//-----------------------------------------------------------------------------

#ifndef UVM_DEFINE_MESSAGE
#define UVM_DEFINE_MESSAGE(id, unused, text) \
 namespace sc_core { extern const char id[]; }
#endif

//
// UVM-SC messages
//

UVM_DEFINE_MESSAGE(UVM_MULTIPLE_STOP_PROCS_    , 1,
        "uvm_component has multiple children named 'stop'; did you mistakenly declare 'SC_THREAD(stop)'?")
UVM_DEFINE_MESSAGE(UVM_PACKER_UNPACK_INDEX_, 2,
        "uvm_packer unpack_index > pack_index")
UVM_DEFINE_MESSAGE(UVM_PACKER_UNPACK_OBJECT_, 3,
        "uvm_packer unpack_object failed")
UVM_DEFINE_MESSAGE(UVM_CREATOR_NOT_FOUND_, 4,
        "uvm creator not found for type")
UVM_DEFINE_MESSAGE(UVM_CREATOR_NOT_OBJECT_, 5,
        "uvm creator is not an object creator")
UVM_DEFINE_MESSAGE(UVM_CREATOR_NOT_COMP_, 6,
        "uvm creator is not a component creator")
UVM_DEFINE_MESSAGE(UVM_OVERRIDE_EXISTS_, 7,
        "uvm type override already exists")
UVM_DEFINE_MESSAGE(UVM_CONFIG_INTERNAL_, 8,
        "uvm config internal error")
UVM_DEFINE_MESSAGE(UVM_UNPACK_DCAST_, 9,
        "DCAST from uvm_object failed in uvm_packer operator >>")
UVM_DEFINE_MESSAGE(UVM_PACK_NULL_, 10,
        "Attempt to pack null uvm_object")
UVM_DEFINE_MESSAGE(UVM_UNPACK_OBJ_NO_METADATA_, 11,
        "Attempt to unpack uvm_object without metadata")

#endif
