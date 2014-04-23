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

#include "bp_type_map.h"
#include "bp_interconnect.h"

using namespace std;

namespace Bp {

uvm_ml_type_id_t FrameworkTypeEntryClass::GetTypeId()
{
    return m_bp_type_map_entry->GetTypeId();
}

void BpTypeMapEntryClass::AddFrmwEntry(FrameworkTypeEntryClass * frmwTypeEntry) 
{ 
    m_matching_types.push_back(frmwTypeEntry);
}

FrameworkTypeEntryClass * BpTypeMapEntryClass::FindFrmwEntry(const FrameworkProxyClass * frmw)
{
    return BpVectorObjectFinder<FrameworkTypeEntryClass, FrameworkComparer, const FrameworkProxyClass *> (m_matching_types, frmw);
}

void BpTypeMapEntryClass::AddFrmwTypeEntry(FrameworkProxyClass * frmw, 
                                           const string        & typeName)
{
    FrameworkTypeEntryClass * frmw_entry = FindFrmwEntry(frmw);
    if (frmw_entry != NULL)
    {
        if (frmw_entry->GetTypeName() == typeName)
            return;
        else
	  BpInterconnect::SERROR2(MLUVM14, "UVM-ML Bp Error: Id = %d, Cannot match two types '%s' and '%s' within the same language\n", frmw_entry->GetTypeName(), typeName);

    }
    AddFrmwEntry(new FrameworkTypeEntryClass(frmw, typeName));
}

}   // namespace Bp
