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

#ifndef UVM_ML_PHASE_SERVICE_H
#define UVM_ML_PHASE_SERVICE_H

#include "bp_common_c.h"
#include <map>
#include <string>

class UvmMlPhaseService
{
public:
   UvmMlPhaseService();
   ~UvmMlPhaseService();

   static UvmMlPhaseService * GetPhaseService();

   void StartPhasing();

   void srvc_notify_phase_done(unsigned int      frameworkId,
                               const char *      phaseGroup,
                               const char *      phaseName,
                               uvm_ml_time_unit  timeUnit,
                               double            timeValue);

private:

    void ExecutePhase(const char *phaseGroup, const char *phaseName);
    void ExecutePhaseRuntime(const char *phaseGroup, const char *phaseName);
    unsigned int m_id;

    std::map<std::string, unsigned int> m_participate;
    std::map<std::string, unsigned int> m_participate_done;
    std::map<std::string, std::string>  m_uvm_runtime_next_phase;

    const char* m_common_grp;
    const char* m_uvm_grp;

    const char* m_build_ph;
    const char* m_connect_ph;
    const char* m_resolve_bindings_ph;
    const char* m_end_of_elaboration_ph;
    const char* m_start_of_simulation_ph;
    const char* m_extract_ph;
    const char* m_check_ph;
    const char* m_report_ph;
    const char* m_final_ph;

    const char* m_run_ph;
    const char* m_reset_ph;
    const char* m_configure_ph;
    const char* m_main_ph;
    const char* m_shutdown_ph;

    double           m_current_time_value;
    uvm_ml_time_unit m_current_time_unit;

    static UvmMlPhaseService * m_phase_service;

};

#endif // UVM_ML_PHASE_SERVICE_H
