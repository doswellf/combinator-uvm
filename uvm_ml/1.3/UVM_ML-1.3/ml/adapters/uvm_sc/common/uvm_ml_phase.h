//----------------------------------------------------------------------
//   Copyright 2013 Advanced Micro Devices Inc.
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

#ifndef UVM_ML_PHASE_H
#define UVM_ML_PHASE_H

#include "bp_provided.h"
#include "base/uvm_common_schedule.h"
#include "base/uvm_phase.h"

using namespace std;
using namespace uvm;

//------------------------------------------------------------------------------
/*! @file uvm_ml_phase.h
 *  Adapter phase header implementing the required phase API.
 */

namespace uvm_ml {


//------------------------------------------------------------------------------
//! ML phase interface for the SC adaptor.
//
class uvm_ml_phase 
{
public:

    static void Initialize(bp_api_struct *bp_provided_api);

    static int  transmit_phase(int                 target_id,
                               const char *        phase_group,
                               const char *        phase_name,
                               uvm_ml_phase_action phase_action);

    static int  notify_phase(const char *        phase_group,
                             const char *        phase_name,
                             uvm_ml_phase_action phase_action);

    static int  notify_runtime_phase(const char *        phase_group,
                                     const char *        phase_name,
                                     uvm_ml_phase_action phase_action,
                                     uvm_ml_time_unit    time_unit,
                                     double              time_value,
                                     unsigned int *      participate);

private:
    static uvm::uvm_common_schedule* get_schedule(const char * phase_group);
    static bool                      is_phase_supported(const char * phase_group, const char * phase_name);
    static void                      wait_barrier(uvm_phase* phase);
    static uvm_phase_state           get_phase_state(uvm_ml_phase_action phase_action);

    static bp_api_struct *  m_bp_provided_api;

}; // class uvm_ml_phase


}   // namespace


#endif  // UVM_ML_PHASE_H
