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

// Backpalne interconnect communication header File
// bp_connection.h

#ifndef BP_CONNECTION_H
#define BP_CONNECTION_H

#include <vector>
#include <string>
#include "bp_utils.h"

using namespace std;

namespace Bp {

enum BpRouteType { UNDEF, TLM1, TLM2 };
enum BpConnectorKind { PORT, EXPORT, IMP, INITIATOR_SOCKET, TARGET_SOCKET };

class FrameworkProxyClass;

/**
* Backplane Connector Descriptor class.
* 
**/
class BpConnectorDescriptorClass 
{
public:
    BpConnectorDescriptorClass(FrameworkProxyClass *  frmw, 
            int                    bindKey, 
            const string &         path, 
            const string &         intfName, 
            BpConnectorKind        kind);
    ~BpConnectorDescriptorClass();

    ///////////////////////////////////////////////////////////////
    // Public Properties
    ///////////////////////////////////////////////////////////////
    
    /**
    * Returns the bind key.
    *
    * @return int - bind key value
    */
    int                    GetBindKey() { return m_bind_key; }
    
    /**
    * Returns the path.
    * @return string - heirachy path name
    */
    const string &         GetPath() { return m_path; }
    
    /**
    * Returns the route type.
    * @return BpRouteType - type of the route
    */
    BpRouteType            GetRouteType() { return m_route_type; }
   
    /**
    * Returns the connector kind.
    * @return BpConnnectorKind - the connector kind
    */
    BpConnectorKind        GetKind() { return m_connector_kind; }
    
    /**
    * Returns a pointer to the framework proxy.
    * @returns ptr - pointer to the framework proxy
    */
    FrameworkProxyClass *  GetFrmw() { return m_framework; }

    /**
     *Returns the interface name
     */
    string GetIntfName() { return m_intf_name; }
    ///////////////////////////////////////////////////////////////

private:
    FrameworkProxyClass *  m_framework;         /**< pointer to framework proxy class*/
    int                    m_bind_key;          /**< bind key value*/
    string                 m_path;              /**< hierachy path name*/
    string                 m_intf_name;         /**< interface name*/
    BpRouteType            m_route_type;        /**< routing type*/
    BpConnectorKind        m_connector_kind;    /**< connector kind*/
};

class BpConnectionClass {
public:
    BpConnectionClass( FrameworkProxyClass *  frmw,
                       int                    bindKey, 
                       const string &         path, 
                       const string &         intfName, 
                       BpConnectorKind        kind);
    ~BpConnectionClass ();

    ///////////////////////////////////////////////////////////////
    // Public Interface
    ///////////////////////////////////////////////////////////////
    //
    bool                       CheckConnected(const BpConnectionClass & provider);
    //
    bool                       CheckCompatibility();
    //
    void                       AddFanout(BpConnectionClass * provider);
    //
    void                       AddFanin(BpConnectionClass * producer);
    //
    BpConnectionClass *        GetSingleProvider();
    //
    BpConnectionClass *        GetSingleProducer();
    ///////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////
    // Public Properties
    ///////////////////////////////////////////////////////////////
    //
    int                    GetBindKey() const { return m_connector_descriptor->GetBindKey(); }
    //
    const string &         GetPath() const { return m_connector_descriptor->GetPath(); }
    //
    BpRouteType            GetRouteType() const { return m_connector_descriptor->GetRouteType(); }
    //
    BpConnectorKind        GetKind() const { return m_connector_descriptor->GetKind(); }
    //
    FrameworkProxyClass *  GetFrmw() const { return m_connector_descriptor->GetFrmw(); }
    //
    string                 GetIntfName() const { return m_connector_descriptor->GetIntfName(); }
    //
    int                    GetSize() { return m_fanout.size(); }
    //
    vector<BpConnectionClass *>& GetFanout() { return m_fanout; }
    //
    vector<BpConnectionClass *>& GetFanin() { return m_fanin; }
    ///////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////

    class PathComparer: public BpStringComparer 
    {
    public:
        PathComparer(string s): BpStringComparer(s) { }
        ~PathComparer() {}
        BpConnectionClass * operator ()( BpConnectionClass *arg) { 
            return ((arg->m_connector_descriptor && arg->m_connector_descriptor->GetPath() == X()) ? arg : (BpConnectionClass *) 0); 
        }
    };

private:
    BpConnectorDescriptorClass * m_connector_descriptor;   
    vector<BpConnectionClass *>  m_fanout;
    vector<BpConnectionClass *>  m_fanin;
};

} // end namespace
#endif /* BP_CONNECTION_H */
