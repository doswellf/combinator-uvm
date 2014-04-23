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
#include "uvm_ml_adapter_imp_spec_headers.h"
#include "uvm_ml_adapter_imp_spec_macros.h"


#define SC_INCLUDE_DYNAMIC_PROCESSES

#include "systemc.h"
#include "sysc/kernel/sc_boost.h"
#include "sysc/kernel/sc_spawn.h"
#include "common/uvm_ml_phase.h"
#include "common/uvm_ml_adapter.h"


#include "base/uvm_common_schedule.h"


namespace uvm_ml {


bp_api_struct * uvm_ml_phase::m_bp_provided_api = NULL;


//------------------------------------------------------------------------------
//! Initialize SC phasing.
/*!
  * @param bp_provided_api - Pointer to Backplane provided API tray
 */
void uvm_ml_phase::Initialize(bp_api_struct *bp_provided_api)
{
    m_bp_provided_api = bp_provided_api;

}   // Initialize()


//------------------------------------------------------------------------------
//! For non-runtime phase notification.
/*!
 *  Called by the backplane to notify a top level component of a phase
 *  or by hierachical parent to notify child of a phase.
 *
 *  When the master phase controller calls bp_notify_phase(), the 
 *  backplane will notify each registered framework of the phase via
 *  notify_phase() and then notify each registered top of the phase
 *  via transmit_phase().
 * 
 *  Some frameworks have phases that applied to the entire framework and 
 *  are not hierarchical, therefore the backplane splits the notify_phase()
 *  called by the master phase controller into two calls.  One to the 
 *  framework (notify_phase), so it can executed any framework specific
 *  phasing and then to the top components (transmit_phase) to do 
 *  hierachical phasing.
 *
 *  In a unified hierarchy, a child proxy is created for a component that
 *  is in another framework. This child proxy is connected through the
 *  backplane to a parent proxy.  All non-time consuming phase notification
 *  the child proxy receieves is passed to the parent proxy through
 *  the bp_transmit_phase() called.  Runtime (time consuming) phases are
 *  non-hierarchical, and are phased by the framework when it recevies
 *  notification.
 * 
 *  @param target_id    - ID of the hierarchical_node to phase from
 *  @param phase_group  - Name of the group/domain the phase belongs to
 *  @param phase_name   - Name of the phase
 *  @param phase_action - Action for this phase (STARTED, EXECTUING, 
 *                        ENDED)
 *  @return Return status
 *          - 1 : success
 *          - 0 : error
 */
int uvm_ml_phase::transmit_phase(int                 target_id,
                                 const char *        phase_group,
                                 const char *        phase_name,
                                 uvm_ml_phase_action phase_action)
{
    uvm_common_schedule * pschedule = get_schedule(phase_group);
    uvm_phase_state       state     = get_phase_state(phase_action);
    sc_core::sc_module  * pmod      = NULL;
    int                   result    = 1;

    if (uvm_ml_utils::is_tree_node_quasi_static(target_id) == false)
        return 1;

    if (is_phase_supported(phase_group, phase_name) == false)
        return 1;

    pmod   = uvm_ml_utils::get_quasi_static_tree_node_by_id(target_id);
    if(pmod == NULL) {
      cout << "UVM_SC adapter: transmit_phase failed, sub-tree not found" << endl;
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: transmit_phase failed, sub-tree not found","");
      return 0;
    };
    result = pschedule->execute_phase(phase_name, state, pmod);

    return result;

}   // transmit_phase()

//------------------------------------------------------------------------------
//! Called by the backplane to notify the framework of a non-runtime phase.
/*!
 *  When the master phase controller calls bp_notify_phase(), the 
 *  backplane will notify each registered framework of the phase via
 *  notify_phase() and then notify each registered top of the phase
 *  via transmit_phase().
 *
 *  The SC adapter to will take care of quasi-static phasing, which is
 *  not hierachical during this time.
 * 
 *  @param phase_group  - Name of the group/domain the phase belongs to
 *  @param phase_name   - Name of the phase
 *  @param phase_action - Action for this phase (STARTED, EXECTUING, 
 *                        ENDED)
 *
 *  @return Return status
 *          - 1 : success
 *          - 0 : error
 */
int uvm_ml_phase::notify_phase(const char *        phase_group,
                               const char *        phase_name,
                               uvm_ml_phase_action phase_action)
{
    uvm_common_schedule * pschedule = get_schedule(phase_group);
    uvm_phase_state       state     = get_phase_state(phase_action);
    int                   result    = 1;

    if (is_phase_supported(phase_group, phase_name) == false)
        return 1;

    result = pschedule->execute_quasi_static_phase(phase_name, state);

    if (result && 
       (strcmp(phase_name, "connect") == 0)  &&
       (state == UVM_PHASE_ENDED) )
    {
        return uvm_ml_utils::do_pending_uvm_ml_connect_calls();
    }

    return result;

}   // notify_phase()

//------------------------------------------------------------------------------
//! Called by the backplane to notify the framework of a runtime (time consuming) phase.
/*!
 *  For runtime phases, the framework could choose to particpate
 *  in the phase or not by setting the participate bit to 1.
 *  If the framework participates in the phase, it means the
 *  phase controller will wait until the framework notifies it
 *  that it is ready to exit the phase (via bp_notify_phase_done)
 *  before continuing to the next phase.
 *
 *  The SC adapter will run a 'delta' cycle (call co_simulate) to allow 
 *  the run_phase processes to executed before checking the barrier count for
 *  the phase. If the barrier count is > 0, or co_simulate did not execute 
 *  (eg. already in in co_sim) then the adapter will set participate to 1, 
 *  and spawn off a wait_barrier() process which will wait for the barrier 
 *  count to reach 0, and call bp_notify_phase_done().
 *   
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param phase_action  - The action for this phase (start, execute,
 *                         ready to end, ended)
 *  @param time_unit     - Current simulation time unit
 *  @param time_value    - Current simulatin time scaled according to time_unit
 *  @param participate   - Indicate the number of frameworks participating in this phase
 *
 *  @return Return status
 *          - 1 : success
 *          - 0 : error
 */
int uvm_ml_phase::notify_runtime_phase(const char *        phase_group,
                                       const char *        phase_name,
                                       uvm_ml_phase_action phase_action,
                                       uvm_ml_time_unit    time_unit,
                                       double              time_value,
                                       unsigned int *      participate)
{
    uvm_common_schedule * pschedule    = get_schedule(phase_group);
    uvm_phase_state       state        = get_phase_state(phase_action);
    uvm_phase *           pphase       = NULL;
    int                   cosim_result = 1;

    (*participate) = 0;

    ENTER_CO_SIMULATION_CONTEXT();

    if (is_phase_supported(phase_group, phase_name) == false)
    {
        EXIT_CO_SIMULATION_CONTEXT();
        return 1;
    }

    pschedule->execute_phase(phase_name, state);
    EXIT_CO_SIMULATION_CONTEXT();

    if (phase_action == UVM_ML_PHASE_EXECUTING)
    {
        cosim_result = CO_SIMULATION_EXECUTE_DELTA();

        uvm_phase * pphase = pschedule->get_current_phase();
        if ((cosim_result == 0) || (pphase->barrier.get_num_barriers() > 0))
        {
            sc_spawn(sc_bind(&wait_barrier, pphase));
            (*participate) = 1;
            return 1;
        }
    }

    return 1;

}   // notify_runtime_phase


//------------------------------------------------------------------------------
//! Handle notifying the phase master when the adapter is ready to exit a phase.
/*!
 *  This method is spawn off during notify_runtime_phase(), if 
 *  any components raise the barrier for that phase.
 *  It will wait for the all barriers to be dropped then call bp_notify_phase_done
 *  to notify the phase master that it is ready to exit the current runtime
 *  phase
 *  
 *  @param pphase - Pointer to phase being monitored
 *
 */
void uvm_ml_phase::wait_barrier(uvm_phase* pphase)
{
    sc_core::wait(SC_ZERO_TIME);
    pphase->barrier.wait();

    sc_core::sc_time current_time  = sc_core::sc_time_stamp();
    double           time_sec      = current_time.to_seconds();
    unsigned         framework_id  = uvm_ml_utils::FrameworkId();
    const char *     phase_name;
    const char *     phase_group;

    phase_name  = pphase->get_name().c_str();
    phase_group = pphase->get_schedule()->basename();

    (*m_bp_provided_api->notify_phase_done_ptr)(framework_id, phase_group, phase_name, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);
    
}   // wait_barrier()


//------------------------------------------------------------------------------
//! Get a pointer to the uvm_sc schedule.
/*!
 *  @param phase_group - Name of the schedule to get (common/uvm).
 *
 *  @return Pointer to the named schedule.
 */
uvm_common_schedule* uvm_ml_phase::get_schedule(const char* phase_group)
{
    uvm_common_schedule * pschedule_common = uvm::get_uvm_common_schedule();
    uvm_common_schedule * pschedule_uvm    = uvm::get_uvm_schedule();

    if (strcmp(phase_group, "common") == 0)
        return pschedule_common;
    else
        return pschedule_uvm;

}   // get_schedule()


//------------------------------------------------------------------------------
//! Returns true if the phase is supported by the SC adapter.
/*!
 *  @param phase_group - Name of the schedule.
 *  @param phase_name  - Name of the phase.
 *
 *  @return Return status
 *          - 1 : Phase supported
 *          - 0 : Phase not supported
 */
bool uvm_ml_phase::is_phase_supported(const char* phase_group, const char*  phase_name)
{
    bool bsupported = false;

    if ( (strcmp(phase_group, "common") == 0) &&
         ( (strcmp(phase_name, "build") == 0)               ||
           (strcmp(phase_name, "connect") == 0)             ||
           (strcmp(phase_name, "resolve_bindings") == 0)    ||
           (strcmp(phase_name, "end_of_elaboration") == 0)  ||
           (strcmp(phase_name, "start_of_simulation") == 0) ||
           (strcmp(phase_name, "run") == 0)                 ||
           (strcmp(phase_name, "extract") == 0)             ||
           (strcmp(phase_name, "check") == 0)               ||
           (strcmp(phase_name, "report") == 0)              ||
           (strcmp(phase_name, "final") == 0)) )
    {
        bsupported = true;
    }
    else if ( (strcmp(phase_group, "uvm") == 0) &&
              ( (strcmp(phase_name, "reset") == 0) ||
                (strcmp(phase_name, "configure") == 0) ||
                (strcmp(phase_name, "main") == 0) ||
                (strcmp(phase_name, "shutdown") == 0)) )
    {
        bsupported = true;
    }

    return bsupported;

}   // is_phase_supported()

//------------------------------------------------------------------------------
//! Translates uvm_ml_phase_action enum to uvm_phase_state enum.
/*!
  * @param phase_action - uvm_ml_phase_action to be converted
  *
  * @return state - uvm_phase_state corresponding to 'phase_action'
 */
uvm_phase_state uvm_ml_phase::get_phase_state(uvm_ml_phase_action phase_action)
{
    uvm_phase_state state;

    switch(phase_action)
    {
    case UVM_ML_PHASE_STARTED:
        state = uvm::UVM_PHASE_READY_TO_START;
        break;
    case UVM_ML_PHASE_EXECUTING:
        state = uvm::UVM_PHASE_EXECUTING;
        break;
    case UVM_ML_PHASE_READY_TO_END:
        state = uvm::UVM_PHASE_READY_TO_END;
        break;
    case UVM_ML_PHASE_ENDED:
        state = uvm::UVM_PHASE_ENDED;
        break;
    default:
        break;
    };

    return state;

}   // get_phase_state()


}   // namespace



