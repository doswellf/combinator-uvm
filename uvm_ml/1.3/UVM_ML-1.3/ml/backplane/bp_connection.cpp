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

#include <algorithm>
#include "bp_connection.h"

namespace Bp {

/**
* Constructor for Backplane connector Descriptor Class.
* This will construct the class required for ....
*
* @param frmw - pointer to framework proxy class
* @param bindkey - bind key
* @param path - path name
* @param intfName - interface name
* @param kind - backplane connector kind
*/
BpConnectorDescriptorClass::BpConnectorDescriptorClass 
(
    FrameworkProxyClass *  frmw,
    int                    bindKey, 
    const string &         path, 
    const string &         intfName, 
    BpConnectorKind        kind): 

    m_framework(frmw),
    m_bind_key(bindKey),
    m_path(path),
    m_intf_name(intfName),
    m_connector_kind(kind)
{
  m_route_type = UNDEF;
}

BpConnectorDescriptorClass::~BpConnectorDescriptorClass()
{
}


BpConnectionClass::BpConnectionClass(FrameworkProxyClass *  frmw,
                                     int                    bindKey, 
                                     const string &         path, 
                                     const string &         intfName, 
                                     BpConnectorKind        kind)
{
    m_connector_descriptor = new BpConnectorDescriptorClass(frmw, 
                                                            bindKey, 
                                                            path, 
                                                            intfName, 
                                                            kind);
}

BpConnectionClass::~BpConnectionClass()
{
}

bool BpConnectionClass::CheckConnected(const BpConnectionClass & providerConnection)
{
    return (std::find(m_fanout.begin(), m_fanout.end(), &providerConnection) != m_fanout.end());
}

void BpConnectionClass::AddFanout(BpConnectionClass * provider)
{
    m_fanout.push_back(provider);
}

void BpConnectionClass::AddFanin(BpConnectionClass * producer)
{
    m_fanin.push_back(producer);
}

bool BpConnectionClass::CheckCompatibility()
{
    // see check_port_registry_intf_compatibility
    // TBD
    return true;
}

BpConnectionClass * BpConnectionClass::GetSingleProvider()
{
    if (m_fanout.size() != 1) 
    {
        // TBD issue an error
        return ((BpConnectionClass *) 0);
    }
    return m_fanout[0];
}

BpConnectionClass * BpConnectionClass::GetSingleProducer()
{
    if (m_fanin.size() != 1) 
    {
        // TBD issue an error
        return ((BpConnectionClass *) 0);
    }
    return m_fanin[0];
}

} // end namespace
