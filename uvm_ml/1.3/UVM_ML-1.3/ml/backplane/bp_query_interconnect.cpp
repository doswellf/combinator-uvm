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
#include <vector>

#include "bp_interconnect.h"
#include "bp_connection.h"

extern void bp_printf(int debug_msg, const char *string,...);

using namespace std;

namespace Bp {

BpConnectionHandle BpInterconnect::FindConnectionHandle(int frameworkId,
                                                        int bindKey)
{
    FrameworkProxyClass * frmw = GetFrameworkRegistry()[frameworkId];
    BpConnectionClass * con = frmw->GetConnection(bindKey);

    vector< BpConnectionClass * >::iterator it;

    unsigned int h;
    for(it = m_port_registry.begin(), h = 0; it != m_port_registry.end(); it++, h++)
    {
        if (*it == con)
            return (BpConnectionHandle) h;
    }
    return (BpConnectionHandle) (-1);
}

int BpInterconnect::QueryFanoutSize(BpConnectionHandle handle) 
{
    BpConnectionClass * con = m_port_registry[handle];
    return con->GetSize();
}

BpConnectionHandle BpInterconnect::QueryFanoutHandle(BpConnectionHandle handle, 
                                                     unsigned int       id) 
{
    BpConnectionClass * con = m_port_registry[handle];
    BpConnectionClass * provider = con->GetFanout()[id];

    vector< BpConnectionClass * >::iterator it;

    unsigned int h;
    for(it = m_port_registry.begin(), h = 0; it != m_port_registry.end(); it++, h++)
    {
        if (*it == provider)
            return (BpConnectionHandle) h;
    }

    bp_printf(BP_ERROR, "Could not locate the port in the registry; ID %d", id);
    assert (false);  // Internal error
    return (-1);
}

int BpInterconnect::QueryFaninSize(BpConnectionHandle handle)
{
    BpConnectionClass * con = m_port_registry[handle];
    return con->GetFanin().size();
}

BpConnectionHandle BpInterconnect::QueryFaninHandle(BpConnectionHandle handle, unsigned int id)
{
    BpConnectionClass * con = m_port_registry[handle];
    BpConnectionClass * producer = con->GetFanin()[id];

    vector< BpConnectionClass * >::iterator it;

    unsigned int h;
    for(it = m_port_registry.begin(), h = 0; it != m_port_registry.end(); it++, h++)
    {
        if (*it == producer)
            return (BpConnectionHandle) h;
    }

    bp_printf(BP_ERROR, "Could not locate the port in the registry; ID %d", id);
    assert (false);  // Internal error
    return (-1);
}

const string & BpInterconnect::QueryFrameworkName(BpConnectionHandle handle)
{
    BpConnectionClass * con = m_port_registry[handle];
    return con->GetFrmw()->GetName();
}

const vector <string> & BpInterconnect::QueryFrameworkIndicators(BpConnectionHandle handle)
{
    BpConnectionClass * con = m_port_registry[handle];
    return con->GetFrmw()->GetIndicators();
}

const string & BpInterconnect::QueryConnectionPath(BpConnectionHandle handle)
{
    BpConnectionClass * con = m_port_registry[handle];
    return con->GetPath();
}

} // end namespace


