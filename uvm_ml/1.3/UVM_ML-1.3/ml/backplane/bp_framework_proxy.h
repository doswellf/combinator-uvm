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

// Framework proxy representation header File
// bp_framework_proxy.h

#ifndef BP_FRAMEWORK_PROXY_H
#define BP_FRAMEWORK_PROXY_H

#include <vector>
#include <map>
#include <strings.h>
#include "bp_utils.h"
#include "bp_c_interface.h"
#include "bp_connection.h"
#include "bp_type_map.h"

using namespace std;

namespace Bp {

class BpTopDescriptorBaseClass;
class BpTopDescriptorClass;

//-------------------------------
//
// CLASS: FrameworkProxyClass
//
// This class transfers the calls from
// the bp to the framework
//
//-------------------------------

class FrameworkProxyClass
{
public:

    FrameworkProxyClass
    (
        int                    id, 
        string &               frameworkName,
        vector<string> &       frameworkIndicators,
        bp_frmw_c_api_struct * requiredApi): 

        m_framework_id(id), 
        m_name(frameworkName),
        m_indicators(frameworkIndicators),
        m_required_api(requiredApi),
        m_trace_mode(0) 
    {
        m_supports_true_blocking = false;
        m_supports_fake_blocking = true;
	//        for (int j = 0; j < frameworkIndicators.size(); j++)
	//	    m_indicators.push_back(frameworkIndicators[j]);
        AddIndicatorsMap();
    };
    ~FrameworkProxyClass() {};

    ///////////////////////////////////////////////////////////////
    // Framework Proxy Properties
    ///////////////////////////////////////////////////////////////
    //
    int                    GetFrameworkId() { return m_framework_id; }
    //
    const string &         GetName() { return m_name; }
    //
    const vector<string> & GetIndicators() { return m_indicators; }
    //
    unsigned               GetTopLevelsN() { return m_top_level_components.size(); }
    ///////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////
    // Public Interface Methods
    // These methods are invoking the C API function tray elements
    ///////////////////////////////////////////////////////////////
    //
    void                       SetTraceMode(int mode);
    //
    void                       Startup();
    //
    int                        InstantiateTopLevel(const string & componentTypeName, const string & instanceName);
    //
    string                     GetTopComponentForArg(const string & arg);
    //
    int                        GetConnectionBindKey(string path);
    //
    string                     GetConnectionIntfName(int bindKey);
    //
    BpConnectorKind            GetConnectionKind(int bindKey);
    //
    void                       ExternalConnect(int bindKey);

    // GetTypeId searches for known id for given type name. If not found creates a new one and returns it
    uvm_ml_type_id_t           GetTypeId(const string & typeName);
    //
    // FindTypeId searches for known id for given type name. If not found returns (-1)
    uvm_ml_type_id_t           FindTypeId(const string & typeName);
    //
    void                       AddRegisteredTypeEntry(const string        & typeName, 
                                                      BpTypeMapEntryClass * typeMapEntry);
    //
    // FindRegisteredTypeEntry searches for registered type entry id for given id. If not found returns NULL
    BpTypeMapEntryClass *      FindRegisteredTypeEntry(uvm_ml_type_id_t typeId);
    //
    string                     GetTypeName(uvm_ml_type_id_t typeId,
                                           bool             getBaseName);
    // 
    bool                       SupportsTrueBlocking() { return m_supports_true_blocking; };
    //
    bool                       SupportsFakeBlocking() { return m_supports_fake_blocking; };

    int  TransmitPhase(int                 targetId,
                       const char *        phaseGroup,
                       const char *        phaseName,
                       uvm_ml_phase_action phaseAction);

    int  NotifyPhase(const char *        phaseGroup,
                     const char *        phaseName,
                     uvm_ml_phase_action phaseAction);

    int  NotifyRuntimePhase(const char *        phaseGroup,
                            const char *        phaseName,
                            uvm_ml_phase_action phaseAction,
                            uvm_ml_time_unit    timeUnit,
                            double              timeValue,
                            unsigned int *      participate);

    void StartPhasing();

    void  PhaseSrvNotifyPhaseDone(unsigned int      frameworkId,
                                  const char *      phaseGroup,
                                  const char *      phaseName,
                                  uvm_ml_time_unit  timeUnit,
                                  double            timeValue);

    //////////////////////////////////////////////////////////////////////////////////
    //                    TLM1 Core Interface methods
    //////////////////////////////////////////////////////////////////////////////////
    //
    int                    NbPut(int              bindKey, 
                                 unsigned int     streamSize,
                                 uvm_ml_stream_t  stream, 
                                 uvm_ml_time_unit timeUnit, 
                                 double           timeValue);
    //
    int                    CanPut(int              bindKey, 
                                  uvm_ml_time_unit timeUnit, 
                                  double           timeValue);
    //
    int                    NbGet(int              bindKey,
                                 unsigned int &   streamSize,
                                 uvm_ml_stream_t  stream, 
                                 uvm_ml_time_unit timeUnit, 
                                 double           timeValue);
    //
    int                    CanGet(int              bindKey, 
                                  uvm_ml_time_unit timeUnit, 
                                  double           timeValue);
    //
    int                    NbPeek(int              bindKey,
                                  unsigned int &   streamSize,
                                  uvm_ml_stream_t  stream, 
                                  uvm_ml_time_unit timeUnit, 
                                  double           timeValue);
    //
    int                    CanPeek(int              bindKey, 
                                   uvm_ml_time_unit timeUnit, 
                                   double           timeValue);
    //
    void                   Write(int              bindKey,
                                 unsigned int     streamSize,
                                 uvm_ml_stream_t  stream, 
                                 uvm_ml_time_unit timeUnit, 
                                 double           timeValue);
    //
    int                    Put(int                bindKey,
                               unsigned int       streamSize,
                               uvm_ml_stream_t    stream, 
                               uvm_ml_time_unit & timeUnit, 
                               double           & timeValue);
    //
    int                    RequestPut(int              bindKey,
                                      int              requestId,
                                      int              callerFrameworkId,
                                      unsigned int     streamSize,
                                      uvm_ml_stream_t  stream, 
                                      uvm_ml_time_unit timeUnit, 
                                      double           timeValue);
    //
    int                    Get(int                bindKey,
                               unsigned int &     streamSize,
                               uvm_ml_stream_t    stream, 
                               uvm_ml_time_unit & timeUnit, 
                               double           & timeValue);
    //
    int                    RequestGet(int              bindKey,
                                      int              requestId,
                                      int              callerFrameworkId, 
                                      uvm_ml_time_unit timeUnit, 
                                      double           timeValue);
    //
    unsigned int           GetRequested(int              bindKey,
                                        int              requestId,
                                        uvm_ml_stream_t  stream);
    //
    int                    Peek(int                bindKey,
                                unsigned int &     streamSize,
                                uvm_ml_stream_t    stream, 
                                uvm_ml_time_unit & timeUnit, 
                                double           & timeValue);
    //
    int                    RequestPeek(int              bindKey,
                                       int              requestId,
                                       int              callerFrameworkId, 
                                       uvm_ml_time_unit timeUnit, 
                                       double           timeValue);
    //
    unsigned int           PeekRequested(int              bindKey,
                                         int              requestId,
                                         uvm_ml_stream_t  stream);
    //
    int                    TransportTLM1(int                bindKey,
                                         unsigned int       reqStreamSize,
                                         uvm_ml_stream_t    reqStream,
                                         unsigned int     & respStreamSize,
                                         uvm_ml_stream_t  & respStream, 
                                         uvm_ml_time_unit & timeUnit, 
                                         double           & timeValue);
    //
    int                    RequestTransportTLM1(int               bindKey,
                                                int               requestId,
                                                int               callerFrameworkId,
                                                unsigned int      reqStreamSize,
                                                uvm_ml_stream_t   reqStream,
                                                unsigned int    & respStreamSize,
                                                uvm_ml_stream_t & respStream, 
                                                uvm_ml_time_unit  timeUnit, 
                                                double            timeValue);
    // 
    int                    TransportTLM1Response(int               bindKey,
                                                 int               requestId,
                                                 uvm_ml_stream_t & respStream);
    //
    int                    NbTransportTLM1(int              bindKey,
                                           unsigned int     reqStreamSize,
                                           uvm_ml_stream_t  reqStream,
                                           unsigned int &   respStreamSize,
                                           uvm_ml_stream_t  respStream, 
                                           uvm_ml_time_unit timeUnit, 
                                           double           timeValue);    
    //
    void                   NotifyEndBlocking(int              requestId, 
                                             uvm_ml_time_unit timeUnit, 
                                             double           timeValue);
    //
    //////////////////////////////////////////////////////////////////////////////////
    //                    TLM2 Interface methods
    //////////////////////////////////////////////////////////////////////////////////
    //
    int                    BTransportTLM2(int                bindKey,
                                          unsigned int     & streamSize,
                                          uvm_ml_stream_t  & stream,
                                          uvm_ml_time      & delay, 
                                          uvm_ml_time_unit & timeUnit, 
                                          double           & timeValue);
    // Thread-spawning blocking call
    int                    RequestBTransportTLM2(int               bindKey,
                                                 int               requestId,
                                                 int               callerFrameworkId,
                                                 unsigned int    & streamSize,
                                                 uvm_ml_stream_t & stream,
                                                 uvm_ml_time     & delay, 
                                                 uvm_ml_time_unit  timeUnit, 
                                                 double            timeValue);
    // Spawned blocking call completion
    // Returns 0 if the task was disabled
    int                    BTransportTLM2Response(int               bindKey,
                                                  int               requestId,
                                                  unsigned int    & streamSize,
                                                  uvm_ml_stream_t & stream);
  
    //
    uvm_ml_tlm_sync_enum   NbTransportFwTLM2(int                bindKey,
                                             unsigned int     & streamSize,
                                             uvm_ml_stream_t  & stream,
                                             uvm_ml_tlm_phase & phase,
                                             unsigned int       transactionId,
                                             uvm_ml_time      & delay, 
                                             uvm_ml_time_unit   timeUnit, 
                                             double             timeValue);
    //
    uvm_ml_tlm_sync_enum   NbTransportBwTLM2(int                bindKey,
                                             unsigned int     & streamSize,
                                             uvm_ml_stream_t  & stream,
                                             uvm_ml_tlm_phase & phase,
                                             unsigned int       transactionId,
                                             uvm_ml_time      & delay, 
                                             uvm_ml_time_unit   timeUnit, 
                                             double             timeValue);
    //
    unsigned int           TransportDbgTLM2(int                bindKey,
                                            unsigned int     & streamSize,
                                            uvm_ml_stream_t  & stream, 
                                            uvm_ml_time_unit   timeUnit, 
                                            double             timeValue);
    //
    void                   TurnOffTransactionMapping(string socketName);
    //
    void                   Synchronize(uvm_ml_time_unit timeUnit, 
                                       double           timeValue);

    //
    //////////////////////////////////////////////////////////////////////////////////
    //                    ML Hierarchical Construction method
    //////////////////////////////////////////////////////////////////////////////////
    //
    int CreateChildJunctionNode(const string & componentTypeName,
                                const string & instanceName,
                                const string & parentFullName,
                                int            parentFrameworkId,
                                int            parentJunctionNodeId);

    ///////////////////////////////////////////////////////////////

    //
    //////////////////////////////////////////////////////////////////////////////////
    //                    ML Configuration Propagation method
    //////////////////////////////////////////////////////////////////////////////////
    //
    void NotifyConfig(const char *     cntxt,
                      const char *     instance_name,
                      const char *     field_name,
                      unsigned int     stream_size,
                      uvm_ml_stream_t  stream,
                      uvm_ml_time_unit time_unit, 
                      double           time_value);

    ///////////////////////////////////////////////////////////////
    // Implementation Service Methods
    ///////////////////////////////////////////////////////////////
    //
    BpTopDescriptorClass * AddTopLevel(const BpTopDescriptorBaseClass * compArg);
    //
    void                   PushTopLevel(BpTopDescriptorClass * comp) 
                                        { m_top_level_components.push_back(comp); }
    //
    void                   AddConnection(BpConnectionClass * con, int bindKey);
    //
    bool                   CheckConnection(const BpConnectionClass & producerConnection,
                                           const BpConnectionClass & providerConnection);
    //
    BpConnectionClass *    GetConnection (int bindKey);
    // 
    bool                   IsQualifiedName(const string & name);
    //
    string                 GetShortName(const string & qualifiedName);
    //
    void                   AddIndicatorsMap();
    //

    class FrameworkNameComparer: public BpStringComparer 
    {
    public:
        FrameworkNameComparer(string s): BpStringComparer(s) { }
        ~FrameworkNameComparer() {}
        bool operator ()(FrameworkProxyClass *arg) { return (strcasecmp(arg->m_name.c_str(), X().c_str()) == 0); }
    };

    ///////////////////////////////////////////////////////////////

private:
    int            m_framework_id;
    string         m_name;
    vector<string> m_indicators;
    int            m_trace_mode;

    vector<BpTopDescriptorClass *>                               m_top_level_components;
    map<int    /* BindKey */, BpConnectionClass *>               m_connections;
    map<string /* Type Name */, int /* Type Id */ >              m_type_entries;
    map<uvm_ml_type_id_t /* Type Id */, string /* Type Name */ > m_type_names;
    map<uvm_ml_type_id_t /* Type Id */, BpTypeMapEntryClass * /* Registered Type Map Entry */ > m_registered_types;
    bp_frmw_c_api_struct *                                       m_required_api;

    bool m_supports_true_blocking;
    bool m_supports_fake_blocking;
};

}
#endif /* BP_FRAMEWORK_PROXY_H */
