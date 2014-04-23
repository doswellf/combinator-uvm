//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
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

#include "bp_c_interface.h"
#include "bp_interconnect.h"
#include "bp_top_descriptor.h"
#include <iostream>

using namespace std;

namespace Bp {

void BpTopDescriptorBaseClass::SetFrameworkTopLevelComponent()
{
    FrameworkProxyClass * frmwProxy = BpInterconnect::GetFrameworkProxyByInd(GetFrameworkIndicator());
    if (!frmwProxy) 
    {
        BpInterconnect::SERROR2(MLUVM05, "UVM-ML Bp Error: Id = %d, -uvmtest or -uvmtop argument '%s' has been specified in language '%s', but no adapter for that language has been registered\n", GetIdentifier(), GetFrameworkIndicator());
        return;
        // TBD: Throw exception
    }

    string topName = frmwProxy->GetTopComponentForArg(GetIdentifier());
    if (!topName.empty()) 
      {
	  //We replace the top name if exists and add to list 
	  //Temporay, till we support type and instance name as valid parameter
       	  if (topName != GetIdentifier()) {
	    SetInstanceName(topName);
	  }
	  BpTopDescriptorClass * topComponent = frmwProxy->AddTopLevel(this);
      }
}

int BpTopDescriptorClass::Instantiate()
{
    if (m_top_level_id == (-1)) 
    {
        // This component was specified on the command line and was not instantiated yet
        m_top_level_id = m_frmw_proxy->InstantiateTopLevel(GetIdentifier(), GetInstanceName());
    }
    return m_top_level_id;
}

int BpTopDescriptorClass::TransmitPhase (const char *        phaseGroup,
                                         const char *        phaseName,
                                         uvm_ml_phase_action phaseAction)
{
    return m_frmw_proxy->TransmitPhase(GetTopLevelId(), phaseGroup, phaseName, phaseAction);
}

} // end namespace
