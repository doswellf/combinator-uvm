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

#include <iostream>
#include "bp_framework_proxy.h"
#include "bp_interconnect.h"
#include "bp_top_descriptor.h"
#include "bp_utils.h"

using namespace std;
extern void bp_printf(int debug_msg, const char *string,...);

namespace Bp {

#define BP_FRMW_CALL_VOID(F) \
  if (m_required_api->F##_ptr) \
    (*(m_required_api->F##_ptr))
  // TBD else throw an error

#define BP_FRMW_CALL(F, TYPE)       \
  TYPE result;                \
  if (m_required_api->F##_ptr) \
    result = (*(m_required_api->F##_ptr))
  // TBD else throw an error

void FrameworkProxyClass::AddIndicatorsMap()
{
    for (int j = 0; j < m_indicators.size(); j++)
        BpInterconnect::AddFrmwIndicator(m_indicators[j], this);
}

void FrameworkProxyClass::Startup()
{
    BP_FRMW_CALL(startup,int)();
    if (result == 0) // failure status
        throw 0;
}

int FrameworkProxyClass::InstantiateTopLevel(const string & componentTypeName, const string & instanceName)
{
    BP_FRMW_CALL(construct_top,int)((const char *)componentTypeName.c_str(), (const char *)instanceName.c_str());
    return result;
}

string FrameworkProxyClass::GetTopComponentForArg(const string & arg)
{
    char * result = NULL;
    if (m_required_api->get_top_component_for_arg_ptr) {
      result = (*(m_required_api->get_top_component_for_arg_ptr))((char *) arg.c_str());
    } else {
      //In case adapter didn't implement the method we simply return the same arg
      return arg;
    }

    if (result) {
      return string(result);
    } else {
      return "";
    }
      
}

// Temporary Patch
static bool isSupportedPhase(const string & frmwName, const char * phaseName)
{
  return ((frmwName != "Specman") ||
          (strcmp(phaseName, "build") == 0) ||
          (strcmp(phaseName, "connect") == 0) ||
	  (strcmp(phaseName, "resolve_bindings")  == 0) ||
	  (strcmp(phaseName, "end_of_elaboration") == 0) ||
	  (strcmp(phaseName, "start_of_simulation") == 0));
}

int FrameworkProxyClass::TransmitPhase
(
    int                 targetId,
    const char *        phaseGroup,
    const char *        phaseName,
    uvm_ml_phase_action phaseAction
)
{
    BP_FRMW_CALL(transmit_phase, int)(targetId, phaseGroup, phaseName, phaseAction);
    return result;
}

int FrameworkProxyClass::NotifyPhase
(
    const char *        phaseGroup,
    const char *        phaseName,
    uvm_ml_phase_action phaseAction
)
{
    BP_FRMW_CALL(notify_phase, int)(phaseGroup, phaseName, phaseAction);
    return result;
}

int FrameworkProxyClass::NotifyRuntimePhase
(
    const char *        phaseGroup,
    const char *        phaseName,
    uvm_ml_phase_action phaseAction,
    uvm_ml_time_unit    timeUnit,
    double              timeValue,
    unsigned int *      participate
)
{

    BP_FRMW_CALL(notify_runtime_phase, int)(phaseGroup, phaseName, phaseAction, timeUnit, timeValue, participate);
    return result;
}

void FrameworkProxyClass::StartPhasing()
{
    BP_FRMW_CALL_VOID(phase_srv_start)();
}

void FrameworkProxyClass::PhaseSrvNotifyPhaseDone
(
    unsigned int      frameworkId,
    const char *      phaseGroup,
    const char *      phaseName,
    uvm_ml_time_unit  timeUnit,
    double            timeValue
)
{
    BP_FRMW_CALL_VOID(phase_srv_notify_phase_done)(frameworkId, phaseGroup, phaseName, timeUnit, timeValue);
}

int FrameworkProxyClass::GetConnectionBindKey(string path)
{
    BP_FRMW_CALL(find_connector_id_by_name, int)((char *) path.c_str());
    return result;
}

string FrameworkProxyClass::GetConnectionIntfName(int bindKey)
{
    BP_FRMW_CALL(get_connector_intf_name, const char *)(bindKey);
    return string(result);
}

BpConnectorKind FrameworkProxyClass::GetConnectionKind(int bindKey)
{
    BP_FRMW_CALL(get_connector_type, int)(bindKey);
    else {
        unsigned is_export = (*(m_required_api->is_export_connector_ptr))(bindKey);
        if (is_export) return EXPORT;
        else return PORT;
    }

    if (result == 0) return PORT;
    else if (result == 1) return EXPORT;
    else if (result == 2) return IMP;
    else if (result == 3) return INITIATOR_SOCKET;
    else return TARGET_SOCKET;
}

void FrameworkProxyClass::ExternalConnect(int bindKey)
{
    BP_FRMW_CALL_VOID(external_connect)(bindKey);
}

void FrameworkProxyClass::AddConnection(BpConnectionClass * con, int bindKey)
{
    m_connections[bindKey] = con;
}


BpConnectionClass * FrameworkProxyClass::GetConnection(int bindKey)
{
    map<int, BpConnectionClass *>::iterator it = m_connections.find(bindKey);
    if (it != m_connections.end())
        return it->second;
    else
        return NULL; // Legal situation if an export (or "imp") remained unbound
}

bool FrameworkProxyClass::CheckConnection(const BpConnectionClass & producerConnection,
                                          const BpConnectionClass & providerConnection)
{
    // TBD - add framework-specific connection checks
    return true;
}

bool FrameworkProxyClass::IsQualifiedName(const string & name)
{
    return (name.find(string("::"),0) != string::npos);
}

string FrameworkProxyClass::GetShortName(const string & name)
{
    int pos = name.rfind(string("::"));
    if (pos == string::npos)
        return name;
    else
        return name.substr(pos+2); // discard the qualifier
}

uvm_ml_type_id_t FrameworkProxyClass::FindTypeId(const string & typeName) 
{
    map<string, int>::iterator it = m_type_entries.find(typeName);

    if (it != m_type_entries.end()) return it->second;
    else if (IsQualifiedName(typeName)) return (-1);
    else { // typeName is short
        uvm_ml_type_id_t res = (-1);
        for ( it = m_type_entries.begin() ; it != m_type_entries.end(); it++ ) {
	    if (GetShortName(it->first) == typeName) {
	      if(res != -1) {
		bp_printf(BP_ERROR, "Type name %s is ambiguous \n there are multiple appearances of the short name in different registered qualified names", typeName.c_str());
	      }
	      assert (res == (-1)); // TODO: issue an error message saying the unqualified type name is ambiguous - 
                                    // there are multiple appearances of the short name in different registered
                                    // qualified names
              res = it->second;
	    }
        }
        return res;
    }
}

void FrameworkProxyClass::AddRegisteredTypeEntry(const string        & typeName, 
                                                 BpTypeMapEntryClass * typeMapEntry)
{
    uvm_ml_type_id_t typeId = typeMapEntry->GetTypeId();

    m_registered_types[typeId] = typeMapEntry;
    m_type_entries[typeName] = typeId;
    m_type_names[typeId] = typeName;
}

BpTypeMapEntryClass * FrameworkProxyClass::FindRegisteredTypeEntry(uvm_ml_type_id_t typeId)
{
    return BpGetMapSecondObject<uvm_ml_type_id_t, BpTypeMapEntryClass>(m_registered_types, typeId);
}

uvm_ml_type_id_t FrameworkProxyClass::GetTypeId(const string & typeName) 
{
    uvm_ml_type_id_t typeId = FindTypeId(typeName); // This function searches for either a full match
                                                    // or, if typeName is short, the single match 
                                                    // among the short parts of the registered qualified names

    if (typeId != (-1))
        return typeId;

    string short_name = GetShortName(typeName);
    if (IsQualifiedName(typeName)) 
    {
        map<string, int>::iterator it = m_type_entries.find(short_name); // Check if the short name was registered
        if (it != m_type_entries.end()) 
            typeId = it->second;
    }
    if (typeId != (-1))
        return typeId;

    // If we got to this point it means the type name appears for the first time for this framework. 
    // It was not registered via RegisterTypeMatch and it was not used by this framework before.
    // Hence this type name is either completely new to the bp or it was used by another
    // framework as an unregistered name (that shall be mapped by exact string match)

    typeId = BpInterconnect::GetUnregisteredTypeId(short_name); // will be found or added
    m_type_entries[short_name] = typeId; // Default mapping is presumed only for the short names
    m_type_names[typeId] = typeName;
    return typeId;
}

string FrameworkProxyClass::GetTypeName(uvm_ml_type_id_t typeId,
                                        bool             getBaseName) 
{
    string typeName;

    map<uvm_ml_type_id_t, string>::iterator it = m_type_names.find(typeId);
    if (it != m_type_names.end())
        typeName = it->second;
    else
        // If we got to this point it means the typeId is new to the FrameworkProxy
        // That means it was not registered with RegisterTypeMatch but rather it was used
        // by another framework as an unregistered type name (meaning the default exact type name match)
        typeName = BpInterconnect::FindUnregisteredTypeName(typeId);

    if (getBaseName)
        return BpExtractBaseName(typeName);
    else
        return typeName;
}

int FrameworkProxyClass::NbPut(int              bindKey, 
                               unsigned int     streamSize,
                               uvm_ml_stream_t  stream,
                               uvm_ml_time_unit timeUnit,
                               double           timeValue)
{
    BP_FRMW_CALL(try_put_uvm_ml_stream, int)(bindKey, streamSize, stream, timeUnit, timeValue);
    return result;
}

int  FrameworkProxyClass::CanPut(int              bindKey,
                                 uvm_ml_time_unit timeUnit,
                                 double           timeValue)
{
    BP_FRMW_CALL(can_put, int)(bindKey, timeUnit, timeValue);
    return result;
}

int  FrameworkProxyClass::NbGet(int              bindKey,
                                unsigned int &   streamSize,
                                uvm_ml_stream_t  stream,
                                uvm_ml_time_unit timeUnit,
                                double           timeValue)
{
    BP_FRMW_CALL(try_get_uvm_ml_stream, int)(bindKey, &streamSize, stream, timeUnit, timeValue);
    return result;
}

int  FrameworkProxyClass::CanGet(int              bindKey,
                                 uvm_ml_time_unit timeUnit,
                                 double           timeValue)
{
    BP_FRMW_CALL(can_get, int)(bindKey, timeUnit, timeValue);
    return result;
}

int  FrameworkProxyClass::NbPeek(int              bindKey,
                                 unsigned int &   streamSize,
                                 uvm_ml_stream_t  stream,
                                 uvm_ml_time_unit timeUnit,
                                 double           timeValue)
{
    BP_FRMW_CALL(try_peek_uvm_ml_stream, int)(bindKey, &streamSize, stream, timeUnit, timeValue);
    return result;
}

int  FrameworkProxyClass::CanPeek(int              bindKey,
                                  uvm_ml_time_unit timeUnit,
                                  double           timeValue)
{
    BP_FRMW_CALL(can_peek, int)(bindKey, timeUnit, timeValue);
    return result;
}

void  FrameworkProxyClass::Write(int              bindKey,
                                 unsigned int     streamSize,
                                 uvm_ml_stream_t  stream,
                                 uvm_ml_time_unit timeUnit,
                                 double           timeValue)
{
    BP_FRMW_CALL_VOID(write_uvm_ml_stream)(bindKey, streamSize, stream, timeUnit, timeValue);
}

int  FrameworkProxyClass::Put(int                bindKey,
                              unsigned int       streamSize,
                              uvm_ml_stream_t    stream,
                              uvm_ml_time_unit & timeUnit,
                              double           & timeValue)
{
    bp_printf(BP_ERROR, "Put not implemented");
    assert(false);
}

int FrameworkProxyClass::RequestPut(int              bindKey,
                                    int              requestId,
                                    int              callerFrameworkId,
                                    unsigned int     streamSize,
                                    uvm_ml_stream_t  stream,
                                    uvm_ml_time_unit timeUnit,
                                    double           timeValue)
{
    BP_FRMW_CALL(put_uvm_ml_stream_request, int)(bindKey, requestId, callerFrameworkId, streamSize, stream, timeUnit, timeValue);
    return result;
}

int FrameworkProxyClass::Get(int                bindKey,
                             unsigned int &     streamSize,
                             uvm_ml_stream_t    stream,
                             uvm_ml_time_unit & timeUnit,
                             double           & timeValue)
{
    BP_FRMW_CALL(get_uvm_ml_stream, int)(bindKey, &streamSize, stream, &timeUnit, &timeValue);
    return result;
}

int FrameworkProxyClass::RequestGet(int              bindKey,
                                    int              requestId,
                                    int              callerFrameworkId,
                                    uvm_ml_time_unit timeUnit,
                                    double           timeValue)
{
    BP_FRMW_CALL(get_uvm_ml_stream_request, int)(bindKey, requestId, callerFrameworkId, timeUnit, timeValue);
    return result;
}

unsigned int FrameworkProxyClass::GetRequested(int             bindKey,
                                               int             requestId,
                                               uvm_ml_stream_t stream)
{
    BP_FRMW_CALL(get_requested_uvm_ml_stream, unsigned int)(bindKey, requestId, stream);
    // Returns stream size
    return result;
}

int  FrameworkProxyClass::Peek(int                bindKey,
                               unsigned int &     streamSize,
                               uvm_ml_stream_t    stream,
                               uvm_ml_time_unit & timeUnit,
                               double           & timeValue)
{
    BP_FRMW_CALL(peek_uvm_ml_stream, int)(bindKey, &streamSize, stream, &timeUnit, &timeValue);
    return result;
}

int FrameworkProxyClass::RequestPeek(int              bindKey,
                                     int              requestId,
                                     int              callerFrameworkId,
                                     uvm_ml_time_unit timeUnit,
                                     double           timeValue)
{
    BP_FRMW_CALL(peek_uvm_ml_stream_request, int)(bindKey, requestId, callerFrameworkId, timeUnit, timeValue);
    return result;
}

unsigned int FrameworkProxyClass::PeekRequested(int              bindKey,
                                                int              requestId,
                                                uvm_ml_stream_t  stream)
{
    BP_FRMW_CALL(peek_requested_uvm_ml_stream, unsigned int)(bindKey, requestId, stream);
    // Returns stream size
    return result;
}
 
int  FrameworkProxyClass::TransportTLM1(int                bindKey,
                                        unsigned int       reqStreamSize,
                                        uvm_ml_stream_t    reqStream,
                                        unsigned int   &   respStreamSize,
                                        uvm_ml_stream_t&   respStream,
                                        uvm_ml_time_unit & timeUnit,
                                        double           & timeValue)
{
    bp_printf(BP_ERROR, "TLM1 Transport not implemented");
    assert(false);
}

int FrameworkProxyClass::RequestTransportTLM1(int               bindKey,
                                              int               requestId,
                                              int               callerFrameworkId,
                                              unsigned int      reqStreamSize,
                                              uvm_ml_stream_t   reqStream,
                                              unsigned int    & respStreamSize,
                                              uvm_ml_stream_t & respStream,
                                              uvm_ml_time_unit  timeUnit,
                                              double            timeValue)
{
    BP_FRMW_CALL(transport_uvm_ml_stream_request, int)(bindKey, requestId, callerFrameworkId, reqStreamSize, reqStream, &respStreamSize, respStream, timeUnit, timeValue);
    return result;
}

int FrameworkProxyClass::TransportTLM1Response(int               bindKey,
                                               int               requestId,
                                               uvm_ml_stream_t & respStream)
{
    BP_FRMW_CALL(transport_response_uvm_ml_stream, int)(bindKey, requestId, respStream);
    return result;
}

int  FrameworkProxyClass::NbTransportTLM1(int              bindKey,
                                          unsigned int     reqStreamSize,
                                          uvm_ml_stream_t  reqStream,
                                          unsigned int &   respStreamSize,
                                          uvm_ml_stream_t  respStream,
                                          uvm_ml_time_unit timeUnit,
                                          double           timeValue)    
{
    BP_FRMW_CALL(nb_transport_uvm_ml_stream, int)(bindKey, reqStreamSize, reqStream, &respStreamSize, respStream, timeUnit, timeValue);
    return result;
}

void FrameworkProxyClass::NotifyEndBlocking(int              requestId,
                                            uvm_ml_time_unit timeUnit,
                                            double           timeValue)
{
    BP_FRMW_CALL_VOID(notify_end_blocking)(requestId, timeUnit, timeValue);
}

int FrameworkProxyClass::BTransportTLM2(int                bindKey,
                                        unsigned int     & streamSize,
                                        uvm_ml_stream_t  & stream,
                                        uvm_ml_time      & delay,
                                        uvm_ml_time_unit & timeUnit,
                                        double           & timeValue)
{
    bp_printf(BP_ERROR, "TLM2 b_transport not implemented");
    assert(false); // true blocking is not supported yet
}

int FrameworkProxyClass::RequestBTransportTLM2(int               bindKey,
                                               int               requestId,
                                               int               callerFrameworkId,
                                               unsigned int    & streamSize,
                                               uvm_ml_stream_t & stream,
                                               uvm_ml_time     & delay,
                                               uvm_ml_time_unit  timeUnit,
                                               double            timeValue)
{
    BP_FRMW_CALL(tlm2_b_transport_request,int)(bindKey, requestId, callerFrameworkId, streamSize, stream, delay.units, delay.value, timeUnit, timeValue);
    return result;
}

int FrameworkProxyClass::BTransportTLM2Response(int               bindKey,
                                                int               requestId,
                                                unsigned int    & streamSize,
                                                uvm_ml_stream_t & stream)
{
    BP_FRMW_CALL(tlm2_b_transport_response,int)(bindKey, requestId, &streamSize, &stream);
    return result;
}

uvm_ml_tlm_sync_enum FrameworkProxyClass::NbTransportFwTLM2(int                bindKey,
                                                            unsigned int     & streamSize,
                                                            uvm_ml_stream_t  & stream,
                                                            uvm_ml_tlm_phase & phase,
                                                            unsigned int       transactionId,
                                                            uvm_ml_time      & delay,
                                                            uvm_ml_time_unit   timeUnit,
                                                            double             timeValue)
{
    BP_FRMW_CALL(tlm2_nb_transport_fw,uvm_ml_tlm_sync_enum)(bindKey,&streamSize,&stream,&phase,transactionId,&delay.units,&delay.value,timeUnit,timeValue);
    return result;
}

uvm_ml_tlm_sync_enum FrameworkProxyClass::NbTransportBwTLM2(int                bindKey,
                                                            unsigned int     & streamSize,
                                                            uvm_ml_stream_t  & stream,
                                                            uvm_ml_tlm_phase & phase,
                                                            unsigned int       transactionId,
                                                            uvm_ml_time      & delay,
                                                            uvm_ml_time_unit   timeUnit,
                                                            double             timeValue)
{
    BP_FRMW_CALL(tlm2_nb_transport_bw,uvm_ml_tlm_sync_enum)(bindKey,&streamSize,&stream,&phase,transactionId,&delay.units,&delay.value,timeUnit,timeValue);
    return result;
}

unsigned int FrameworkProxyClass::TransportDbgTLM2(int                bindKey,
                                                   unsigned int     & streamSize,
                                                   uvm_ml_stream_t  & stream, 
                                                   uvm_ml_time_unit   timeUnit, 
                                                   double             timeValue)
{
    BP_FRMW_CALL(tlm2_transport_dbg,unsigned int)(bindKey,&streamSize,&stream,timeUnit,timeValue);
    return result;
}

void FrameworkProxyClass::TurnOffTransactionMapping(string socketName)
{
    BP_FRMW_CALL_VOID(tlm2_turn_off_transaction_mapping)(socketName.c_str());
}

void FrameworkProxyClass::Synchronize(uvm_ml_time_unit timeUnit, 
                                      double           timeValue)
{
    BP_FRMW_CALL_VOID(synchronize)(timeUnit, timeValue);
}

BpTopDescriptorClass * FrameworkProxyClass::AddTopLevel(const BpTopDescriptorBaseClass * compArg) 
{
    BpTopDescriptorClass * comp;
    
    comp = new BpTopDescriptorClass(compArg, this);
    BpInterconnect::AddTopLevel(comp);
    PushTopLevel(comp);

    return comp;
}

void FrameworkProxyClass::SetTraceMode(int mode)
{
    if (m_trace_mode != mode) 
    {
        (*(m_required_api->set_trace_mode_ptr))(mode);
        m_trace_mode = mode;
    } 
}

int FrameworkProxyClass::CreateChildJunctionNode(const string & componentTypeName,
                                                 const string & instanceName,
                                                 const string & parentFullName,
                                                 int            parentFrameworkId,
                                                 int            parentJunctionNodeId)
{
    BP_FRMW_CALL(create_child_junction_node,int)(componentTypeName.c_str(), instanceName.c_str(), 
                                                 parentFullName.c_str(), parentFrameworkId, parentJunctionNodeId);
    // result is the parent proxy ID
    return result;
}

void FrameworkProxyClass::NotifyConfig(const char *     cntxt,
                                       const char *     instance_name,
                                       const char *     field_name,
                                       unsigned int     stream_size,
                                       uvm_ml_stream_t  stream,
                                       uvm_ml_time_unit time_unit, 
                      double           time_value)
{
    BP_FRMW_CALL_VOID(notify_config)(cntxt, instance_name, field_name, stream_size, stream, time_unit, time_value);
}
                 
} // end namespace
