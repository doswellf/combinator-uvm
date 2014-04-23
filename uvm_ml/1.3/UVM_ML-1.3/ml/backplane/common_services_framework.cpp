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
#include "common_services_framework.h"
#include "bp_interconnect.h"
#include <iostream>


using namespace std;

namespace Bp
{

CommonServicesFramework* CommonServicesFramework::m_common_services_frmw = GetCommonSrvFrmw();
UvmMlPhaseService*       CommonServicesFramework::m_phase_service        = 0;

///////////////////////////////////////////////////////////////////////
/// CommonServicesFramework Singleton.
/// Returns a pointer to CommonServicesFramework
///
/// @return CommonServicesFramework - pointer to singleton
///
///////////////////////////////////////////////////////////////////////
CommonServicesFramework* CommonServicesFramework::GetCommonSrvFrmw()
{
    string                 name = "Common Services";
    vector<string>         indicator;
    bp_frmw_c_api_struct * requiredApi = getRequiredApi();

    indicator.push_back("Common Services");

    if (m_common_services_frmw == 0) {
        m_common_services_frmw = new CommonServicesFramework(name, indicator, requiredApi);
    }
    return m_common_services_frmw;
}


///////////////////////////////////////////////////////////////////////
/// CommonServicesFramework Constructor.
///
/// Register itself with the backplane and also register phasing
/// services.
/// 
///////////////////////////////////////////////////////////////////////
CommonServicesFramework::CommonServicesFramework(string               & frameworkName, 
                                                 vector<string>       & frameworkIndicators, 
                                                 bp_frmw_c_api_struct * requiredApi ) :

    FrameworkProxyClass(-1, frameworkName, frameworkIndicators, requiredApi)
{
    
    bp_srv_provider_struct srv_provider;
    srv_provider.phase_srv_provider = GetName().c_str(); 

    BpInterconnect::RegisterCommonSrvFrmw(this);
    BpInterconnect::RegisterSrvProviders(GetFrameworkId(), &srv_provider);
}

///////////////////////////////////////////////////////////////////////
/// CommonServicesFramework Destructor.
///
///////////////////////////////////////////////////////////////////////
CommonServicesFramework::~CommonServicesFramework()
{
}

///////////////////////////////////////////////////////////////////////
/// Calls UvmMlPhaseService to start phasing.
///
///////////////////////////////////////////////////////////////////////
void CommonServicesFramework::phase_srv_start()
{
    m_phase_service = UvmMlPhaseService::GetPhaseService();
    m_phase_service->StartPhasing();
}

///////////////////////////////////////////////////////////////////////
/// Calls UvmMlPhaseService to notify of phase done.
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
void CommonServicesFramework::phase_srv_notify_phase_done(
    unsigned int      frameworkId,
    const char *      phaseGroup,
    const char *      phaseName,
    uvm_ml_time_unit  timeUnit,
    double            timeValue)
{
    m_phase_service->srvc_notify_phase_done(frameworkId, phaseGroup, phaseName, timeUnit, timeValue);
}

///////////////////////////////////////////////////////////////////////
/// Gets the required API tray
///
///////////////////////////////////////////////////////////////////////
bp_frmw_c_api_struct * CommonServicesFramework::getRequiredApi()
{
    bp_frmw_c_api_struct * requiredApi = new bp_frmw_c_api_struct();

    memset(requiredApi, '\0', sizeof(bp_frmw_c_api_struct));    // init struct

    requiredApi->phase_srv_start_ptr             = CommonServicesFramework::phase_srv_start;
    requiredApi->phase_srv_notify_phase_done_ptr = CommonServicesFramework::phase_srv_notify_phase_done;

    return requiredApi;
}


}  // namespace Bp







