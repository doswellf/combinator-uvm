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

#include <iostream>
#include <string.h>
#include <algorithm>
#include <functional>

#include "bp_utils.h"
#include "bp_interconnect.h"

extern void bp_printf(int debug_msg, const char *string,...);

namespace Bp {

BpChildProxyClass::BpChildProxyClass(const string & instanceName,
                                     const string & parentFullName,
                                     int            targetFrameworkId)
{
    m_target_framework_id = targetFrameworkId;
    m_full_name = parentFullName + "." + instanceName;
}

int BpInterconnect::CreateChildJunctionNode(int            frameworkId,
                                            const string & targetFrameworkIndicator,
                                            const string & componentTypeName,
                                            const string & instanceName,
                                            const string & parentFullName,
                                            int            parentJunctionNodeId)
{
    FrameworkProxyClass * targetFrmw = BpInterconnect::GetFrameworkProxyByInd(targetFrameworkIndicator);
    if(targetFrmw == NULL) {
      bp_printf(BP_ERROR, "No framework with name '%s' has been registered", targetFrameworkIndicator.c_str());
      return -1;
    };
    //assert (targetFrmw != NULL); // TODO: add proper error message no framework with this name was registered
    int result = targetFrmw->CreateChildJunctionNode(componentTypeName, 
                                                     instanceName, 
                                                     parentFullName,
                                                     frameworkId,
                                                     parentJunctionNodeId);
    if (result >= 0) {
        m_child_proxy_registry.push_back(new BpChildProxyClass(instanceName, 
                                                               parentFullName,
                                                               targetFrmw->GetFrameworkId()));
    }
    return result;
}

} // namespace Bp
