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


#include "bp_interconnect.h"
#include "bp_top_descriptor.h"

extern void bp_printf(int debug_msg, const char *string,...);

namespace Bp {

bool BpInterconnect::RegisterRoute(int         frameworkId, 
                                   string      producerPath, 
                                   string      providerPath)
{
    BpConnectionClass * producerConnection = FindConnectionByName(producerPath);
    if (!producerConnection)
    {
        if ((producerConnection = AddConnection(producerPath)) == (BpConnectionClass * )0)
            return false;
    }

    BpConnectionClass * providerConnection = FindConnectionByName(providerPath);
    if (!providerConnection)
    {
        if ((providerConnection = AddConnection(providerPath)) == (BpConnectionClass * )0)
            return false;
    }

    if (producerConnection->CheckConnected(*providerConnection) == false) 
    {

        if ((checkConnectionDirections(*producerConnection, *providerConnection) == false) ||
                (producerConnection->GetFrmw()->CheckConnection(*producerConnection, *providerConnection) == false) ||
                (providerConnection->GetFrmw()->CheckConnection(*producerConnection, *providerConnection) == false))
            return false;

        producerConnection->AddFanout(providerConnection);
        providerConnection->AddFanin(producerConnection);
    }
    producerConnection->GetFrmw()->ExternalConnect(producerConnection->GetBindKey());
    providerConnection->GetFrmw()->ExternalConnect(providerConnection->GetBindKey());
    return true;
}

bool operator > (const BpConnectionClass & producer, 
                 const BpConnectionClass & provider)
{
    if(producer.GetRouteType() != provider.GetRouteType()) {
      bp_printf(BP_ERROR, "Cannot compare connections when route type is different");
    };
    assert (producer.GetRouteType() == provider.GetRouteType());
    // It is assumed that the match of the GetRouteType()'s is pre-checked

    switch (producer.GetKind()) 
    {
    case PORT:
        return false; // Port can serve as a producer for any TLM1 connection
    case EXPORT:
        return (provider.GetKind() < EXPORT); // An export cannot serve as a producer for a port
    case IMP:
        return true; // An imp canot be a producer
    case INITIATOR_SOCKET:
        return (provider.GetKind() != TARGET_SOCKET); // initiator to initiator connection is not allowed
    case TARGET_SOCKET:
        return true; // A target connector cannot be a producer
    default:
        return true;
    }
}

bool BpInterconnect::checkConnectionDirections(const BpConnectionClass & producer, 
                                               const BpConnectionClass & provider)
{
    if (producer.GetRouteType() != provider.GetRouteType()) 
    {
        SERROR2(MLUVM07, "UVM-ML Bp Error: Id = %d, Mismatching ML OVM connectors. The 1st argument is %s and the 2nd argument is %s\n", ((producer.GetRouteType() == TLM1) ? "TLM1" : "TLM2"), ((provider.GetRouteType() == TLM1) ? "TLM1" : "TLM2"));
        return false;
    }

    if (producer.GetIntfName() != provider.GetIntfName()) {
      if ((((producer.GetIntfName() == "tlm_blocking_put") || (producer.GetIntfName() == "tlm_nonblocking_put")) && 
	   provider.GetIntfName() == "tlm_put") || 
	  (((producer.GetIntfName() == "tlm_blocking_get") || (producer.GetIntfName() == "tlm_nonblocking_get")) && 
	   provider.GetIntfName() == "tlm_get") ||
	  (((producer.GetIntfName() == "tlm_blocking_peek") || (producer.GetIntfName() == "tlm_nonblocking_peek")) && 
	   provider.GetIntfName() == "tlm_peek") ||
	  (((producer.GetIntfName() == "tlm_blocking_transport") || (producer.GetIntfName() == "tlm_nonblocking_transport")) && 
	   provider.GetIntfName() == "tlm_transport") ||
	  (((producer.GetIntfName() == "tlm_blocking_get_peek") || (producer.GetIntfName() == "tlm_nonblocking_get_peek")) && 
	   provider.GetIntfName() == "tlm_get_peek") ||
	  (((producer.GetIntfName() == "tlm_blocking_get") || (producer.GetIntfName() == "tlm_blocking_peek")) && 
	   provider.GetIntfName() == "tlm_blocking_get_peek") ||
	  (((producer.GetIntfName() == "tlm_nonblocking_get") || (producer.GetIntfName() == "tlm_nonblocking_peek")) && 
	   provider.GetIntfName() == "tlm_nonblocking_get_peek") ||
 	  (((producer.GetIntfName() == "tlm_blocking_put") || (producer.GetIntfName() == "tlm_blocking_get") || 
	    (producer.GetIntfName() == "tlm_blocking_peek")) && 
	   ((provider.GetIntfName() == "tlm_blocking_master") || (provider.GetIntfName() == "tlm_blocking_slave"))) ||
 	  (((producer.GetIntfName() == "tlm_nonblocking_put") || (producer.GetIntfName() == "tlm_nonblocking_get") || 
	    (producer.GetIntfName() == "tlm_nonblocking_peek")) && 
	   ((provider.GetIntfName() == "tlm_nonblocking_master") || (provider.GetIntfName() == "tlm_nonblocking_slave"))) ||
 	  (((producer.GetIntfName() == "tlm_blocking_put") || 
	    (producer.GetIntfName() == "tlm_nonblocking_put") || 
	    (producer.GetIntfName() == "tlm_put") || 
	    (producer.GetIntfName() == "tlm_blocking_get") || 
	    (producer.GetIntfName() == "tlm_nonblocking_get") || 
	    (producer.GetIntfName() == "tlm_get") || 
	    (producer.GetIntfName() == "tlm_peek") || 
	    (producer.GetIntfName() == "tlm_blocking_peek") || 
	    (producer.GetIntfName() == "tlm_nonblocking_peek")) && 
	   ((provider.GetIntfName() == "tlm_master") || (provider.GetIntfName() == "tlm_slave")))
	  ) {
	// OK
      } else {
        SERROR2(MLUVM07, "UVM-ML Bp Error: Id = %d, Mismatching ML connectors. The 1st argument is '%s' and the 2nd argument is '%s'\n", producer.GetIntfName() + " in " + producer.GetPath(), provider.GetIntfName() +  " in " + provider.GetPath());
        return false;
      }
    }

    if (producer > provider) 
    {
      SERROR2(MLUVM07, "UVM-ML Bp Error: Id = %d, Incorrect order of arguments for UVM ML connection function. Arguments are %s and %s\n", producer.GetPath(), provider.GetPath());
        return false;
    } 
    else
    {
        return true;
    }
}

BpConnectionClass * BpInterconnect::GetSingleProvider(int frameworkId,
                                                      int producerBindKey)
{
    FrameworkProxyClass * producerFrmw = GetFramework(frameworkId);

    BpConnectionClass * producer = producerFrmw->GetConnection(producerBindKey);

    if(producer == NULL) {
      bp_printf(BP_ERROR, "Cannot identify producer by ID %d", producerBindKey);
    }
    assert (producer != NULL); // Internal error

    BpConnectionClass * provider = producer->GetSingleProvider();
    if(producer == NULL) {
      bp_printf(BP_ERROR, "Cannot identify unique provider for producer");
    }
    assert (provider != NULL);

    return provider;
}

BpConnectionClass * BpInterconnect::GetSingleProducer(int frameworkId,
                                                      int providerBindKey)
{
    FrameworkProxyClass * providerFrmw = GetFramework(frameworkId);

    BpConnectionClass * provider = providerFrmw->GetConnection(providerBindKey);

    if(provider == NULL) {
      bp_printf(BP_ERROR, "Cannot identify provider by ID %d", providerBindKey);
    }
    assert (provider != NULL); // Internal error

    BpConnectionClass * producer = provider->GetSingleProducer();
    if(provider == NULL) {
      bp_printf(BP_ERROR, "Cannot identify unique producer for provider");
    }
    assert (producer != NULL);

    return producer;
}

bool BpInterconnect::FrameworksCompatibleBlocking(FrameworkProxyClass & frmw1, 
                                                  FrameworkProxyClass & frmw2)
{
    return (frmw1.SupportsTrueBlocking() && frmw2.SupportsTrueBlocking()) || (frmw1.SupportsFakeBlocking() && frmw2.SupportsFakeBlocking());
}

  ////////////////////////////////
  //
  //      TLM1
  //
  ////////////////////////////////
  
int BpInterconnect::NbPut(int              frameworkId,
                          int              producerBindKey,
                          unsigned int     streamSize,
                          uvm_ml_stream_t  stream,
                          uvm_ml_time_unit timeUnit,
                          double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->NbPut(provider->GetBindKey(), streamSize, stream, timeUnit, timeValue);
}

int BpInterconnect::CanPut(int              frameworkId,
                           int              producerBindKey,
                           uvm_ml_time_unit timeUnit,
                           double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->CanPut(provider->GetBindKey(), timeUnit, timeValue);
}

int BpInterconnect::NbGet(int              frameworkId,
                          int              producerBindKey,
                          unsigned int &   streamSize,
                          uvm_ml_stream_t  stream,
                          uvm_ml_time_unit timeUnit,
                          double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->NbGet(provider->GetBindKey(),streamSize,stream, timeUnit, timeValue);  
}

int BpInterconnect::CanGet(int              frameworkId,
                           int              producerBindKey,
                           uvm_ml_time_unit timeUnit,
                           double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->CanGet(provider->GetBindKey(), timeUnit, timeValue);  
}

int BpInterconnect::NbPeek(int              frameworkId,
                           int              producerBindKey,
                           unsigned int &   streamSize,
                           uvm_ml_stream_t  stream,
                           uvm_ml_time_unit timeUnit,
                           double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->NbPeek(provider->GetBindKey(),streamSize,stream, timeUnit, timeValue);  
}

int BpInterconnect::CanPeek(int              frameworkId,
                            int              producerBindKey,
                            uvm_ml_time_unit timeUnit,
                            double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->CanPeek(provider->GetBindKey(), timeUnit, timeValue);  
}

void BpInterconnect::Write(int              frameworkId,
                           int              producerBindKey,
                           unsigned int     streamSize,
                           uvm_ml_stream_t  stream,
                           uvm_ml_time_unit timeUnit,
                           double           timeValue)
{
    FrameworkProxyClass * producerFrmw = GetFramework(frameworkId);

    BpConnectionClass * producer = producerFrmw->GetConnection(producerBindKey);

    if(producer == NULL) {
      bp_printf(BP_ERROR, "Cannot identify unique producer by ID %d", producerBindKey);
    }
    assert (producer != NULL); // Internal error

    vector<BpConnectionClass *>& fanout = producer->GetFanout();
    vector<BpConnectionClass *>::iterator it;
    for (it = fanout.begin(); it != fanout.end(); it++) 
    {
        (*it)->GetFrmw()->Write((*it)->GetBindKey(), streamSize, stream, timeUnit, timeValue);
    }
}

class BlockingCallRequestor {
public:
    BlockingCallRequestor() {}
    ~BlockingCallRequestor() {}

    // Generic method implementing fake blocking call requests
    int  RequestBlockingCall(int                     callerFrameworkId,
                             int                     producerBindKey,
                             int                     requestId,
                             unsigned int &          streamSize,
                             uvm_ml_stream_t         stream,
                             bool &                  useTrueBlocking,
                             uvm_ml_time_unit &      timeUnit,
                             double           &      timeValue,
                             unsigned int *          respstreamSize = NULL,
                             uvm_ml_stream_t         respstream = NULL,
                             uvm_ml_time *           delay = NULL)
  {
      BpConnectionClass * provider = BpInterconnect::GetSingleProvider(callerFrameworkId, producerBindKey);

      // Meantime implemented only the preepmptive blocking call
      assert (BpInterconnect::FrameworksCompatibleBlocking(*BpInterconnect::GetFramework(callerFrameworkId), *(provider->GetFrmw())));
      // TBD: issue a proper error

      if (BpInterconnect::GetFramework(callerFrameworkId)->SupportsTrueBlocking() && provider->GetFrmw()->SupportsTrueBlocking()) 
      {
          useTrueBlocking = true;
          return DoIt(*provider, streamSize, stream, respstreamSize, respstream, delay, timeUnit, timeValue);
      }
      else 
      {
          useTrueBlocking = false;
          return RequestIt(*provider, requestId, callerFrameworkId, streamSize, stream, respstreamSize, respstream, delay, timeUnit, timeValue);
      }
  }

  virtual int DoIt(BpConnectionClass & provider,
                   unsigned int &      streamSize,
                   uvm_ml_stream_t     stream,
                   unsigned int *      respstreamSize,
                   uvm_ml_stream_t     respstream,
                   uvm_ml_time *       delay,
                   uvm_ml_time_unit &  timeUnit,
                   double           &  timeValue) = 0;

  virtual int RequestIt(BpConnectionClass & provider,
                        int                 requestId,
                        int                 callerFrameworkId,
                        unsigned int &      streamSize,
                        uvm_ml_stream_t     stream,
                        unsigned int *      respstreamSize,
                        uvm_ml_stream_t     respstream,
                        uvm_ml_time *       delay,
                        uvm_ml_time_unit    timeUnit,
                        double              timeValue) = 0;
};

class PutRequestorT: public BlockingCallRequestor
{
public:
    int DoIt(BpConnectionClass & provider, 
             unsigned int &      streamSize,
             uvm_ml_stream_t     stream,
             unsigned int *      UNUSED respstreamSize,
             uvm_ml_stream_t     UNUSED respstream,
             uvm_ml_time *       UNUSED delay,
             uvm_ml_time_unit &  timeUnit,
             double           &  timeValue)
    {
        return provider.GetFrmw()->Put(provider.GetBindKey(),streamSize,stream, timeUnit, timeValue);
    }

    int RequestIt(BpConnectionClass & provider, 
                  int                 requestId,
                  int                 callerFrameworkId,
                  unsigned int &      streamSize,
                  uvm_ml_stream_t     stream,
                  unsigned int *      UNUSED respstreamSize,
                  uvm_ml_stream_t     UNUSED respstream,
                  uvm_ml_time *       UNUSED delay,
                  uvm_ml_time_unit    timeUnit,
                  double              timeValue)
    {
        return provider.GetFrmw()->RequestPut(provider.GetBindKey(),requestId,callerFrameworkId,streamSize,stream, timeUnit, timeValue);
    }
};

static PutRequestorT PutRequestor;

class GetRequestorT: public BlockingCallRequestor
{
public:
    int DoIt(BpConnectionClass & provider, 
             unsigned int &      streamSize,
             uvm_ml_stream_t     stream,
             unsigned int *      UNUSED respstreamSize,
             uvm_ml_stream_t     UNUSED respstream,
             uvm_ml_time *       UNUSED delay,
             uvm_ml_time_unit &  timeUnit,
             double           &  timeValue)
    {
        return provider.GetFrmw()->Get(provider.GetBindKey(),streamSize,stream, timeUnit, timeValue);
    }

  int RequestIt(BpConnectionClass & provider, 
                int                 requestId,
                int                 callerFrameworkId,
                unsigned int &      UNUSED streamSize,
                uvm_ml_stream_t     UNUSED stream,
                unsigned int *      UNUSED respstreamSize,
                uvm_ml_stream_t     UNUSED respstream,
                uvm_ml_time *       UNUSED delay,
                uvm_ml_time_unit    timeUnit,
                double              timeValue)
  {
      return provider.GetFrmw()->RequestGet(provider.GetBindKey(),requestId,callerFrameworkId, timeUnit, timeValue);
  }
};

static GetRequestorT GetRequestor;

class PeekRequestorT: public BlockingCallRequestor
{
public:
    int DoIt(BpConnectionClass & provider, 
             unsigned int &      streamSize,
             uvm_ml_stream_t     stream,
             unsigned int *      UNUSED respstreamSize,
             uvm_ml_stream_t     UNUSED respstream,
             uvm_ml_time *       UNUSED delay,
             uvm_ml_time_unit &  timeUnit,
             double           &  timeValue)
    {
        return provider.GetFrmw()->Peek(provider.GetBindKey(),streamSize, stream, timeUnit, timeValue);
    }

  int RequestIt(BpConnectionClass & provider, 
                int                 requestId,
                int                 callerFrameworkId,
                unsigned int &      UNUSED streamSize,
                uvm_ml_stream_t     UNUSED stream,
                unsigned int *      UNUSED respstreamSize,
                uvm_ml_stream_t     UNUSED respstream,
                uvm_ml_time *       UNUSED delay,
                uvm_ml_time_unit    timeUnit,
                double              timeValue)
  {
      return provider.GetFrmw()->RequestPeek(provider.GetBindKey(),requestId,callerFrameworkId, timeUnit, timeValue);
  }
};

static PeekRequestorT PeekRequestor;

class TransportTLM1RequestorT: public BlockingCallRequestor
{
public:
  int DoIt(BpConnectionClass & provider, 
           unsigned int &      streamSize,
           uvm_ml_stream_t     stream,
           unsigned int *      respstreamSize,
           uvm_ml_stream_t     respstream,
           uvm_ml_time *       UNUSED delay,
           uvm_ml_time_unit &  timeUnit,
           double           &  timeValue)
  {
      return provider.GetFrmw()->TransportTLM1(provider.GetBindKey(),streamSize, stream, *respstreamSize, respstream, timeUnit, timeValue);
  }

  int RequestIt(BpConnectionClass & provider, 
                int                 requestId,
                int                 callerFrameworkId,
                unsigned int &      streamSize,
                uvm_ml_stream_t     stream,
                unsigned int *      respstreamSize,
                uvm_ml_stream_t     respstream,
                uvm_ml_time *       UNUSED delay,
                uvm_ml_time_unit    timeUnit,
                double              timeValue)
  {
      return provider.GetFrmw()->RequestTransportTLM1(provider.GetBindKey(),requestId, callerFrameworkId, streamSize, stream, *respstreamSize, respstream, timeUnit, timeValue);
  }
};

static TransportTLM1RequestorT TransportTLM1Requestor;

class BTransportTLM2RequestorT: public BlockingCallRequestor
{
public:
  int DoIt(BpConnectionClass & provider, 
           unsigned int &      streamSize,
           uvm_ml_stream_t     stream,
           unsigned int *      UNUSED respstreamSize,
           uvm_ml_stream_t     UNUSED respstream,
           uvm_ml_time *       delay,
           uvm_ml_time_unit &  timeUnit,
           double           &  timeValue)
  {
      return provider.GetFrmw()->BTransportTLM2(provider.GetBindKey(),streamSize,stream,*delay, timeUnit, timeValue);
  }

  int RequestIt(BpConnectionClass & provider, 
                int                 requestId,
                int                 callerFrameworkId,
                unsigned int &      streamSize,
                uvm_ml_stream_t     stream,
                unsigned int *      UNUSED respstreamSize,
                uvm_ml_stream_t     UNUSED respstream,
                uvm_ml_time *       delay,
                uvm_ml_time_unit    timeUnit,
                double              timeValue)
  {
      return provider.GetFrmw()->RequestBTransportTLM2(provider.GetBindKey(),requestId,callerFrameworkId,streamSize,stream,*delay, timeUnit, timeValue);
  }
};

static BTransportTLM2RequestorT BTransportTLM2Requestor;

int BpInterconnect::Put(int                frameworkId,
                        int                producerBindKey,
                        unsigned int       streamSize,
                        uvm_ml_stream_t    stream,
                        uvm_ml_time_unit & timeUnit,
                        double           & timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->Put(provider->GetBindKey(), streamSize, stream, timeUnit, timeValue);  
}

int BpInterconnect::RequestPut(int                frameworkId,
                               int                producerBindKey,
                               int                requestId,
                               unsigned int       streamSize,
                               uvm_ml_stream_t    stream,
                               bool &             done,
                               uvm_ml_time_unit   timeUnit,
                               double             timeValue)
{
    return PutRequestor.RequestBlockingCall(frameworkId,producerBindKey,requestId,streamSize,stream,done,timeUnit,timeValue);
    // Return value: 1 if the thread was disabled
}

int BpInterconnect::Get(int                frameworkId,
                        int                producerBindKey,
                        unsigned int &     streamSize,
                        uvm_ml_stream_t    stream,
                        uvm_ml_time_unit & timeUnit,
                        double           & timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->Get(provider->GetBindKey(), streamSize, stream, timeUnit, timeValue);  
}

int BpInterconnect::RequestGet(int                frameworkId,
                               int                producerBindKey,
                               int                requestId,
                               unsigned int &     streamSize,
                               uvm_ml_stream_t    stream,
                               bool &             done,
                               uvm_ml_time_unit & timeUnit,
                               double           & timeValue)
{
    return GetRequestor.RequestBlockingCall(frameworkId,producerBindKey,requestId,streamSize,stream,done,timeUnit,timeValue);
}

unsigned int BpInterconnect::GetRequested(int              frameworkId,
                                          int              producerBindKey,
                                          int              requestId,
                                          uvm_ml_stream_t  stream)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    // Returns stream size
    return provider->GetFrmw()->GetRequested(provider->GetBindKey(), requestId, stream);  
}

int BpInterconnect::Peek(int                frameworkId,
                         int                producerBindKey,
                         unsigned int &     streamSize,
                         uvm_ml_stream_t    stream,
                         uvm_ml_time_unit & timeUnit,
                         double           & timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->Peek(provider->GetBindKey(), streamSize, stream, timeUnit, timeValue);  
}

int BpInterconnect::RequestPeek(int                frameworkId,
                                int                producerBindKey,
                                int                requestId,
                                unsigned int &     streamSize,
                                uvm_ml_stream_t    stream,
                                bool &             useTrueBlocking,
                                uvm_ml_time_unit & timeUnit,
                                double           & timeValue)
{
    return PeekRequestor.RequestBlockingCall(frameworkId,producerBindKey,requestId,streamSize,stream,useTrueBlocking, timeUnit, timeValue);
}

unsigned int BpInterconnect::PeekRequested(int              frameworkId,
                                           int              producerBindKey,
                                           int              requestId,
                                           uvm_ml_stream_t  stream)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    // Returns stream size
    return provider->GetFrmw()->PeekRequested(provider->GetBindKey(), requestId, stream);  
}

int BpInterconnect::TransportTLM1(int                frameworkId,
                                  int                producerBindKey,
                                  unsigned int       reqstreamSize,
                                  uvm_ml_stream_t    reqstream,
                                  unsigned int     & respstreamSize,
                                  uvm_ml_stream_t  & respstream,
                                  uvm_ml_time_unit & timeUnit,
                                  double           & timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->TransportTLM1(provider->GetBindKey(), reqstreamSize, reqstream, respstreamSize, respstream, timeUnit, timeValue); 
}

int BpInterconnect::RequestTransportTLM1(int                frameworkId,
                                         int                producerBindKey,
                                         int                requestId,
                                         unsigned int       reqstreamSize,
                                         uvm_ml_stream_t    reqstream,
                                         unsigned int     & respstreamSize,
                                         uvm_ml_stream_t  & respstream,
                                         bool             & useTrueBlocking,
                                         uvm_ml_time_unit & timeUnit,
                                         double           & timeValue)
{
    return TransportTLM1Requestor.RequestBlockingCall(frameworkId,producerBindKey,requestId,reqstreamSize,reqstream,useTrueBlocking, timeUnit, timeValue, &respstreamSize, respstream);
}

  // Spawned blocking call completion
int BpInterconnect::TransportTLM1Response(int               frameworkId,
                                          int               producerBindKey,
                                          int               requestId,
                                          uvm_ml_stream_t & respstream)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    // Returns stream size
    return provider->GetFrmw()->TransportTLM1Response(provider->GetBindKey(), requestId, respstream);  
}

int BpInterconnect::NbTransportTLM1(int              frameworkId,
                                    int              producerBindKey,
                                    unsigned int     reqstreamSize,
                                    uvm_ml_stream_t  reqstream,
                                    unsigned int &   respstreamSize,
                                    uvm_ml_stream_t  respstream,
                                    uvm_ml_time_unit timeUnit,
                                    double           timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, producerBindKey);
    return provider->GetFrmw()->NbTransportTLM1(provider->GetBindKey(), reqstreamSize, reqstream, respstreamSize, respstream, timeUnit, timeValue); 
}

int BpInterconnect::BTransportTLM2(int                frameworkId,
                                   int                initiatorBindKey,
                                   unsigned int     & streamSize,
                                   uvm_ml_stream_t  & stream,
                                   uvm_ml_time      & delay,
                                   uvm_ml_time_unit & timeUnit,
                                   double           & timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, initiatorBindKey);
    return provider->GetFrmw()->BTransportTLM2(provider->GetBindKey(), streamSize, stream, delay, timeUnit, timeValue);
}

int BpInterconnect::RequestBTransportTLM2(int                frameworkId,
                                          int                initiatorBindKey,
                                          int                requestId,
                                          unsigned int     & streamSize,
                                          uvm_ml_stream_t  & stream,
                                          uvm_ml_time      & delay,
                                          bool             & useTrueBlocking,
                                          uvm_ml_time_unit & timeUnit,
                                          double           & timeValue)
{
    return BTransportTLM2Requestor.RequestBlockingCall(frameworkId,initiatorBindKey,requestId,streamSize,stream,useTrueBlocking,timeUnit,timeValue,NULL,NULL,& delay);
}

int BpInterconnect::BTransportTLM2Response(int               frameworkId,
                                           int               initiatorBindKey,
                                           int               requestId,
                                           unsigned int    & streamSize,
                                           uvm_ml_stream_t & stream)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, initiatorBindKey);
    return provider->GetFrmw()->BTransportTLM2Response(provider->GetBindKey(), requestId, streamSize, stream);
}

uvm_ml_tlm_sync_enum BpInterconnect::NbTransportFwTLM2(int                frameworkId,
                                                       int                initiatorBindKey,
                                                       unsigned int     & streamSize,
                                                       uvm_ml_stream_t  & stream,
                                                       uvm_ml_tlm_phase & phase,
                                                       unsigned int       transactionId,
                                                       uvm_ml_time      & delay,
                                                       uvm_ml_time_unit   timeUnit,
                                                       double             timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, initiatorBindKey);
    return provider->GetFrmw()->NbTransportFwTLM2(provider->GetBindKey(), streamSize, stream, phase, transactionId, delay, timeUnit, timeValue);
}

uvm_ml_tlm_sync_enum BpInterconnect::NbTransportBwTLM2(int                frameworkId,
                                                       int                targetBindKey,
                                                       unsigned int     & streamSize,
                                                       uvm_ml_stream_t  & stream,
                                                       uvm_ml_tlm_phase & phase,
                                                       unsigned int       transaction_id,
                                                       uvm_ml_time      & delay,
                                                       uvm_ml_time_unit   timeUnit,
                                                       double             timeValue)
{
    BpConnectionClass * provider = GetSingleProducer(frameworkId, targetBindKey);
    return provider->GetFrmw()->NbTransportBwTLM2(provider->GetBindKey(), streamSize, stream, phase, transaction_id, delay, timeUnit, timeValue);
}

unsigned int BpInterconnect::TransportDbgTLM2(int                frameworkId,
                                              int                targetBindKey,
                                              unsigned int     & streamSize,
                                              uvm_ml_stream_t  & stream,
                                              uvm_ml_time_unit   timeUnit,
                                              double             timeValue)
{
    BpConnectionClass * provider = GetSingleProvider(frameworkId, targetBindKey);
    return provider->GetFrmw()->TransportDbgTLM2(provider->GetBindKey(), streamSize, stream, timeUnit, timeValue);
}

unsigned int BpInterconnect::AssignTransactionId(int frameworkId)
{
    static unsigned int transactionId = 0;
    return transactionId++;
}

void BpInterconnect::TurnOffTransactionMapping(int UNUSED frameworkId, string & socketName)
{
    BpConnectionClass * conn = FindConnectionByName(socketName);
    return conn->GetFrmw()->TurnOffTransactionMapping(socketName);
}

void BpInterconnect::NotifyEndBlocking(int              frameworkId,
                                       int              requestId,
                                       uvm_ml_time_unit timeUnit,
                                       double           timeValue)
{
    GetFramework(frameworkId)->NotifyEndBlocking(requestId, timeUnit, timeValue);
}

void BpInterconnect::Reset()
{
    bp_printf(BP_ERROR, "Reset not implemented");
    assert (false);
}

} // end namespace
