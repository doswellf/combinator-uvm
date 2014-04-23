//----------------------------------------------------------------------
//   Copyright 2012-2013 Advanced Micro Devices Inc.
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

#include "uvm_ml_phase_service.h"
#include "bp_provided.h"
#include "bp_utils.h"
#include <iostream>


using namespace Bp;
using namespace std;

extern "C" 
{
    bp_api_struct * bp_get_provided_tray();
}   // extern 'C'


UvmMlPhaseService* UvmMlPhaseService::m_phase_service = 0;

///////////////////////////////////////////////////////////////////////
/// UvmMlPhaseService Singleton.
/// Returns a pointer to UvmMlPhaseService
///
/// @return UvmMlPhaseService - pointer to singleton
///
///////////////////////////////////////////////////////////////////////
UvmMlPhaseService* UvmMlPhaseService::GetPhaseService() 
{
    if (m_phase_service == 0) {
        m_phase_service = new UvmMlPhaseService();
    }
    return m_phase_service;
}


///////////////////////////////////////////////////////////////////////
/// UvmMlPhaseService Constructor.
///
///////////////////////////////////////////////////////////////////////
UvmMlPhaseService::UvmMlPhaseService() :
    m_id(0)
{
    m_common_grp = "common";
    m_uvm_grp    = "uvm";

    m_build_ph               = "build";
    m_connect_ph             = "connect";
    m_resolve_bindings_ph    = "resolve_bindings";
    m_end_of_elaboration_ph  = "end_of_elaboration";
    m_start_of_simulation_ph = "start_of_simulation";
    m_extract_ph             = "extract";
    m_check_ph               = "check";
    m_report_ph              = "report";
    m_final_ph               = "final";

    m_run_ph       = "run";
    m_reset_ph     = "reset";
    m_configure_ph = "configure";
    m_main_ph      = "main";
    m_shutdown_ph  = "shutdown";

    m_participate[m_run_ph]       = 0;
    m_participate[m_reset_ph]     = 0;
    m_participate[m_configure_ph] = 0;
    m_participate[m_main_ph]      = 0;
    m_participate[m_shutdown_ph]  = 0;

    m_participate_done[m_run_ph]       = 0;
    m_participate_done[m_reset_ph]     = 0;
    m_participate_done[m_configure_ph] = 0;
    m_participate_done[m_main_ph]      = 0;
    m_participate_done[m_shutdown_ph]  = 0;

    m_uvm_runtime_next_phase[m_reset_ph]     = m_configure_ph;
    m_uvm_runtime_next_phase[m_configure_ph] = m_main_ph;
    m_uvm_runtime_next_phase[m_main_ph]      = m_shutdown_ph;
    m_uvm_runtime_next_phase[m_shutdown_ph]  = "";

    m_current_time_value = 0;
    m_current_time_unit  = TIME_UNIT_FS;
}

///////////////////////////////////////////////////////////////////////
/// UvmMlPhaseService Destructor.
///
///////////////////////////////////////////////////////////////////////
UvmMlPhaseService::~UvmMlPhaseService()
{
}

///////////////////////////////////////////////////////////////////////
/// Start running the phase schedule.
///
///////////////////////////////////////////////////////////////////////
void UvmMlPhaseService::StartPhasing()
{
    // Pre-run phases
    ExecutePhase(m_common_grp, m_build_ph);
    ExecutePhase(m_common_grp, m_connect_ph);
    ExecutePhase(m_common_grp, m_resolve_bindings_ph);
    ExecutePhase(m_common_grp, m_end_of_elaboration_ph);
    ExecutePhase(m_common_grp, m_start_of_simulation_ph);
    
    // Runtime phases
    ExecutePhaseRuntime(m_common_grp, m_run_ph);
    ExecutePhaseRuntime(m_uvm_grp, m_reset_ph);
}

///////////////////////////////////////////////////////////////////////
/// Notify the backplane of the non-runtime phases.
///
///////////////////////////////////////////////////////////////////////
void UvmMlPhaseService::ExecutePhase(const char *phaseGroup, const char *phaseName)
{
    int returnValue = 0;
    bp_api_struct * bpApiProvided = bp_get_provided_tray();

    //TODO: check returnValue?
    returnValue = bpApiProvided->notify_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_STARTED);
    returnValue = bpApiProvided->notify_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_EXECUTING);
    returnValue = bpApiProvided->notify_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_ENDED);
}


///////////////////////////////////////////////////////////////////////
/// Notify the backplane of the runtime phases.
/// Keeps track of the number frameworks participating in the phase.
/// Will only move on to the next phase when the number of
/// notify_phase_done() received for the phase is equal to the
/// participate count received here.
///
/// @param phaseGroup   - Name of the group the phase belongs in 
///                       (eg. common, uvm ...)
/// @param phaseName    - Name of the phase
///
///////////////////////////////////////////////////////////////////////
void UvmMlPhaseService::ExecutePhaseRuntime(const char *phaseGroup, const char *phaseName)
{
    unsigned int     participate = 0;
    unsigned int     dummy       = 0;

    bp_api_struct * bpApiProvided = bp_get_provided_tray();
   

    bpApiProvided->notify_runtime_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_STARTED, m_current_time_unit, m_current_time_value, &dummy);
    bpApiProvided->notify_runtime_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_EXECUTING, m_current_time_unit, m_current_time_value, &participate);

    m_participate[string(phaseName)] = participate;
}

///////////////////////////////////////////////////////////////////////
/// Called by the backplane when a phase done notification is
/// initiated by one of the frameworks for a particular phase.
///
/// Check participate counts and execute the next phase when all
/// participating frameworks has notified phase done.
///
/// @param frameworkId  - Unique ID of the framework adapter
/// @param phaseGroup   - Name of the group the phase belongs in 
///                       (eg. common, uvm ...)
/// @param phaseName    - Name of the phase
/// @param phaseAction  - The action for this phase (start, execute,
///                       ready to end, ended)
/// @param timeUnit     - Current simulation time unit
/// @param timeValue    - Current simulatin time scaled according to time_unit
///
///////////////////////////////////////////////////////////////////////
void UvmMlPhaseService::srvc_notify_phase_done
(
    unsigned int      frameworkId,
    const char *      phaseGroup,
    const char *      phaseName,
    uvm_ml_time_unit  timeUnit,
    double            timeValue
)
{
    unsigned int    dummy         = 0;
    bp_api_struct * bpApiProvided = bp_get_provided_tray();
    string          name          = string(phaseName);

    if (timeUnit < TIME_UNIT_UNDEFINED)
    {
        m_current_time_unit  = timeUnit;
        m_current_time_value = timeValue;
    }

    m_participate_done[name]++;

    // Execute the next runtime phase
    if ( (strcmp(phaseName, m_run_ph)) &&
         (m_participate_done[name] == m_participate[name]) )
    {
        bpApiProvided->notify_runtime_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_READY_TO_END, m_current_time_unit, m_current_time_value, &dummy);
        bpApiProvided->notify_runtime_phase_ptr(m_id, phaseGroup, phaseName, UVM_ML_PHASE_ENDED, m_current_time_unit, m_current_time_value, &dummy);
        if (m_uvm_runtime_next_phase[phaseName] != "")
            ExecutePhaseRuntime(m_uvm_grp, m_uvm_runtime_next_phase[name].c_str());
    }

    // Both run phase and shutdown phase has to reached the end
    // before executing post-run phases
    if ((m_participate_done[m_run_ph] == m_participate[m_run_ph]) && 
        (m_participate_done[m_shutdown_ph] == m_participate[m_shutdown_ph]))
    {
        bpApiProvided->notify_runtime_phase_ptr(m_id, m_common_grp, m_run_ph, UVM_ML_PHASE_READY_TO_END, m_current_time_unit, m_current_time_value, &dummy);
        bpApiProvided->notify_runtime_phase_ptr(m_id, m_common_grp, m_run_ph, UVM_ML_PHASE_ENDED, m_current_time_unit, m_current_time_value, &dummy);

        ExecutePhase(m_common_grp, m_extract_ph);
        ExecutePhase(m_common_grp, m_check_ph);
        ExecutePhase(m_common_grp, m_report_ph);
        ExecutePhase(m_common_grp, m_final_ph);
    }
}






