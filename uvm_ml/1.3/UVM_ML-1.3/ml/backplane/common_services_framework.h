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

#ifndef COMMON_SERVICES_FRAMEWORK_H
#define COMMON_SERVICES_FRAMEWORK_H

#include "bp_framework_proxy.h"

class UvmMlPhaseService;

namespace Bp {

class CommonServicesFramework: public FrameworkProxyClass
{
public:
   CommonServicesFramework(string               & frameworkName, 
                           vector<string>       & frameworkIndicators, 
                           bp_frmw_c_api_struct * requiredApi );

   ~CommonServicesFramework();

   static CommonServicesFramework * GetCommonSrvFrmw();

   static void phase_srv_start();
   static void phase_srv_notify_phase_done(unsigned int      frameworkId,
                                           const char *      phaseGroup,
                                           const char *      phaseName,
                                           uvm_ml_time_unit  timeUnit,
                                           double            timeValue);


private:

    static CommonServicesFramework * m_common_services_frmw;
    static UvmMlPhaseService *       m_phase_service;

    static bp_frmw_c_api_struct * getRequiredApi();

};

}  // BP namspace

#endif // COMMON_SERVICES_FRAMEWORK_H
