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
#include <vector>
#include <string>
#include "bp_common_c.h"
#include "bp_provided.h"
#include "bp_interconnect.h"

using namespace std;
using namespace Bp;

#define BP_DEBUG_LEVEL 1


/*! @addtogroup BP_Provided Backplane provided API
 *
 *  @brief API provided by the backplane to the framework adapters.
 *  @{
 */


/// @cond PRIVATE
//------------------------------------------------------------------------------
// void bp_printf(int debug_msg, const char *string,...)
//
// Temporory trace printout function

void bp_printf(int debug_msg, const char *string,...)
{
    va_list args;

    if ((debug_msg <= BP_DEBUG_LEVEL) || BpInterconnect::GetTraceMode()) 
    {
        va_start (args, string);
        fflush (stdout);
        switch(debug_msg)
        {
        case BP_ERROR:
            fprintf (stderr, "UVM-ML BP_ERROR >> ");
            break;
        case BP_WARNING:
            fprintf (stderr, "UVM-ML BP_WARNING >> ");
            break;
        case BP_DEBUG:
            fprintf (stderr, "UVM-ML BP_DEBUG >> ");
            break;
        };
        vfprintf (stderr, string, args);
        fprintf (stderr, "\n");
    }
}
/// @endcond

extern "C" {

//------------------------------------------------------------------------------
//! Returns a pointer to the backplane provided API tray.
/*! GetProvidedTray() shall be invoked first in order to obtain an access
 *  to BP Provided API
 * 
 *  @return bp_api_struct* - structure containing extern 'C' function 
 *                           pointers to the backplane provided APIs.
 */
bp_api_struct * bp_get_provided_tray()
{
    return BpInterconnect::GetProvidedTray();
}


//******************************************************************************
// -----  Backplane and frameworks setup API
//******************************************************************************

//------------------------------------------------------------------------------
//! Set the debugging mode for all frameworks.
/*! Each framework can invoke bp_set_trace_mode() and BP will broadcasts
 *  this request to turn on/off the UVM ML activities tracing
 * 
 *  @param mode - 1 : print debug msg;
 *                0 : do not print debug msg
 *              
 */
void bp_set_trace_mode(int mode)
{
    BpInterconnect::SetTraceMode(mode);
}


//------------------------------------------------------------------------------
//! Register a framework with the backplane.
/*! Shall be invoked by each participating framework.  It creates an 
 *  internal framework proxy object in BP framework registry.
 * 
 *  @param framework_name       - Name of the framework. A voluntary 
 *                                string (ideally it shall be unique
 *                                for each framework. This string is 
 *                                used only for tracing
 *  @param framework_indicators - Each framework shall be associated 
 *                                with one or more 
 *                                short string names (indicators). These 
 *                                indicators are used by the integrator to 
 *                                denote the framework
 *  @param framework_api        - Pointer to the structure containing the
 *                                function pointers to the framework API 
 *                                required by the backplane
 * 
 *  @return 
 *      - If successful, returns a unique framework ID. 
 *      - Otherwise (-1) in case of error.
 * 
 */
int bp_register_framework(char *                 framework_name,
                          char *                 framework_indicators[],
                          bp_frmw_c_api_struct * framework_api)
{
    string frmwName = framework_name;
    vector<string> frmwIndicators;

    for (int j = 0; framework_indicators[j] != 0 && framework_indicators[j][0] != '\0'; j++)
      frmwIndicators.push_back(string(framework_indicators[j]));

    int res = BpInterconnect::RegisterFramework(frmwName, frmwIndicators, framework_api);
    if (getenv("UVM_ML_DEBUG_MODE"))
        BpInterconnect::SetTraceMode(1);

    return res;
}

//------------------------------------------------------------------------------
//! Returns the backplane version number.
/*! 
 *  @return Version number for the current backplane.
 * 
 */
char * bp_get_version() 
{
  char * result = const_cast<char *> (BpInterconnect::GetVersion().c_str());
  bp_printf(BP_DEBUG,
            "In bp_get_version(). Returned version is %s\n", result);
  return result;
}


//------------------------------------------------------------------------------
//! Register a root node with backplane.
/*! Allows a framework to add a root node descriptor procedurally 
 *  (rather than as an argument of bp_run_test() or Bootstrap())
 * 
 *  @param adapter_id     - Unique ID of the framework adapter the root node is in
 *  @param top_level_id   - ID of the root node (unique for this framework)
 *  @param component_name - Type identifier name of the root node
 *  @param instance_name  - Instance name of the root node (to be used in 
 *                          a full hierarchical name)
 * 
 *  @return Returns with one of the following codes:
 *           -  1   : if root node was added
 *           -  0   : if it was already register before
 *           - (-1) : error (eg. if another root node was already registered with
 *                    the same instance name)
 * 
 */
int bp_add_root_node (unsigned     adapter_id, 
                      unsigned     top_level_id, 
                      const char * component_name,
                      const char * instance_name) 
{ 
    string componentName = component_name;
    string instanceName  = instance_name;
    return BpInterconnect::AddRootNode(adapter_id, top_level_id, componentName, instanceName);
}

//------------------------------------------------------------------------------
//! Start running the ML testbench.
/*!
 *  @param framework_id - ID of the framework adapter initiating the call
 *  @param tops_n       - The number of top level components this test has
 *  @param tops         - Array of strings containing the name of the all
 *                        the top level components
 *  @param test         - Name of the top level test component, if one exists
 * 
 */
int bp_run_test(int framework_id, int tops_n, char ** tops, char * test)
{

    bp_printf(BP_DEBUG, "In bp_run_test() called by framework %d\n", framework_id);

    vector<string> topStr;

    for (int j = 0; j < tops_n; j++)
      if (tops[j][0] != '\0')
          topStr.push_back(string (tops[j]));

    vector<string> testStr; // BpInterconnect::ProcessTopsAndTests() accepts a vector and issues an error if has more than 1 element
    
    if (test != NULL && test[0] != '\0')
        testStr.push_back(string (test));

    try {
        Bp::BpInterconnect::ProcessTopsAndTests(topStr, testStr);
    }
    catch (int ) 
    {
        // TBD: Add a message arguments parsing failed
        return 0;
    }
    return Bp::BpInterconnect::Elaborate(NULL);   
}

//------------------------------------------------------------------------------
//! Broadcast RESET condition through backplane
/*! Currently not supported.
 */
static void bp_reset()
{
    bp_printf(BP_ERROR, "Reset not implemented");
    assert (false);
}


//******************************************************************************
// ----- Framework synchronization API
//******************************************************************************

//------------------------------------------------------------------------------
//! Synchronize simulation time between frameworks.
/*!
 *  @param framework_id - ID of the framework adapter initiating the call
 *  @param time_unit    - Simulation time unit
 *  @param time_value   - Current simulatin time
 * 
 */
void bp_synchronize(int framework_id, uvm_ml_time_unit time_unit, double time_value)
{
    BpInterconnect::Synchronize(framework_id, time_unit, time_value);
}


//******************************************************************************
// ----- TLM Common API
//******************************************************************************

//------------------------------------------------------------------------------
//! Connect two connectors together.
/*! Shall be invoked by a framework to connect ML TLM ports/export/sockets
 *  (e.g. port<->export, initiator_socket<->target_socket)
 * 
 *  @param framework_id - ID of the framework adapter initiating the call
 *  @param path1        - Full hierarchical path of the first connector
 *  @param path2        - Full hierarchical path of the second connector
 * 
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 * 
 */
unsigned bp_connect(unsigned       framework_id, 
                    const char *   path1,
                    const char *   path2)
{
    bp_printf(BP_DEBUG, "In bp_connect() called by framework %d for producer_path = %s provider_path = %s\n", framework_id, path1, path2);
    unsigned result = BpInterconnect::RegisterRoute(framework_id, path1, path2);
    bp_printf(BP_DEBUG, "In bp_connect() result = %d\n", result);
    return result;
}

//------------------------------------------------------------------------------
//* Returns the size of a connector.
/*!
 *  @param framework_id - ID of the framework the connector belongs to
 *  @param connector_id - ID of the connector
 * 
 */
int bp_get_connector_size(int framework_id, int connector_id) 
{
  int result = BpInterconnect::GetConnectorSize(framework_id,connector_id); 
  bp_printf(BP_DEBUG,"In bp_get_connector_size() for framework %d with connector_id %d. Result is: %d\n",
		  framework_id,connector_id,result);
  return result;
}


//------------------------------------------------------------------------------
//! Notify the task with 'call_id' has ended.
/*! Part of the pseudo-blocking mechanism of bp_request*()/bp_notify_end_task() 
 *  When a blocking process terminates, the provider adapter invokes 
 *  bp_notify_end_task() and notifies the producer adapter that the method completed.
 * 
 *  @param framework_id          - ID of the framework adapter invoking the call
 *  @param callback_framework_id - ID of the framework waiting for the callback
 *  @param call_id               - ID of the process that was blocked
 *  @param time_unit             - Simulation time unit
 *  @param time_value            - Current simulatin time
 * 
 */
void bp_notify_end_blocking(int              framework_id,
                            int              callback_framework_id, 
                            int              call_id,
                            uvm_ml_time_unit time_unit,
                            double           time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_notify_end_blocking() called by framework %d\n", framework_id);
    BpInterconnect::NotifyEndBlocking(callback_framework_id, call_id, time_unit, time_value);
}


//******************************************************************************
// ----- TLM1 put API
//******************************************************************************

//------------------------------------------------------------------------------
//! TLM1 non-blocking put interface method.
/*!
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param stream_size  - Size (in words) of the serialized data stream
 *  @param stream       - Serialize data
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 * 
 */
int bp_nb_put(int              framework_id,
              int              producer_id,
              unsigned int     stream_size,
              uvm_ml_stream_t  stream,
              uvm_ml_time_unit time_unit,
              double           time_value)
{
    bp_printf(BP_DEBUG, "In bp_nb_put()\n");
    return BpInterconnect::NbPut(framework_id, producer_id, stream_size, stream, time_unit, time_value);
}

//------------------------------------------------------------------------------
//! TLM1 can_put interface method.
/*!
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 * 
 */
int bp_can_put(int              framework_id, 
	       int              producer_id,
	       uvm_ml_time_unit time_unit,
	       double           time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_can_put()\n");
    return BpInterconnect::CanPut(framework_id, producer_id, time_unit, time_value);
}

//------------------------------------------------------------------------------
//! TLM1 blocking put interface method.
/*! This native blocking call is not supported.
 *  The pseudo-blocking mechanism of RequestPut()/NotifyEndTask() 
 *  should be used instead.
 * 
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param stream_size  - Size (in words) of the serialized data stream
 *  @param stream       - Serialize data
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Returns 0 - unsupported.
 * 
 */
int bp_put(int                framework_id,
           int                producer_id,
           unsigned int       stream_size,
           uvm_ml_stream_t    stream,
           uvm_ml_time_unit * time_unit,
           double           * time_value)
{
    bp_printf(BP_DEBUG, "In bp_put()\n");
    bp_printf(BP_ERROR, "Put not implemented");
    assert (false);
    return 0;
}

//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking put interface method. 
 *  This method calls the corresponding BpConnect class method which 
 *  spawns a thread (forks off a process) that can block through 
 *  a framework adapter. When the process terminates the provider adapter
 *  invokes bp_notify_end_task() and notifies the producer adapter that the 
 *  method completed.
 * 
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param call_id      - Unique ID, assigned to this call by the producer framework adapter
 *  @param stream_size  - Size (in words) of the serialized data stream
 *  @param stream       - Serialize data
 *  @param done         - an output parameter; The provider adapter shall assign it 
 *                        true if the call was completed immediately (did not block)
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Return status :
 *          - 0 - if the blocking calls completes normally
 *          - 1 - if the corresponding thread was disabled before normal completion
 * 
 */
int bp_request_put(int                framework_id,
                   int                producer_id,
                   int                call_id, 
                   unsigned int       stream_size, 
                   uvm_ml_stream_t    stream,
                   unsigned int     * done,
                   uvm_ml_time_unit * time_unit,
                   double           * time_value) 
{
    // Time_unit and time_value are passed by pointer in anticipation that some implementations may support true blocking mode
    bp_printf(BP_DEBUG, "In bp_request_put()\n");
    bool done_tmp = false;
    int result = BpInterconnect::RequestPut(framework_id, producer_id, call_id, stream_size, stream, done_tmp, *time_unit, *time_value);
    *done = done_tmp; 
    return result;
}




//******************************************************************************
// ----- TLM1 get API
//******************************************************************************


//------------------------------------------------------------------------------
//! TLM1 non-blocking get interface method.
/*!
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param producer_id      - Connection ID on the producer's framework adapter side
 *  @param stream_size_ptr  - Return Value : Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 * 
 */
int bp_nb_get(int               framework_id, 
              int               producer_id,
              unsigned int   *  stream_size_ptr,
              uvm_ml_stream_t   stream,
              uvm_ml_time_unit  time_unit,
              double            time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_nb_get()\n");
    return BpInterconnect::NbGet(framework_id, producer_id, *stream_size_ptr, stream, time_unit, time_value);
}

//------------------------------------------------------------------------------
//! TLM1 can_get interface method.
/*!
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 * 
 */
int bp_can_get(int              framework_id, 
               int              producer_id,
               uvm_ml_time_unit time_unit,
               double           time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_can_get()\n");
    return BpInterconnect::CanGet(framework_id, producer_id, time_unit, time_value);
}

//------------------------------------------------------------------------------
//! TLM1 blocking get interface method.
/*! This native blocking call is not supported.
 *  The pseudo-blocking mechanism of RequestGet()/NotifyEndTask() 
 *  should be used instead.
 * 
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param stream       - Serialize data
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Return 0 - unsupported.
 */
int bp_get(int                framework_id,
           int                producer_id,
           uvm_ml_stream_t    stream,
           uvm_ml_time_unit * time_unit,
           double           * time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_get()\n");
    bp_printf(BP_ERROR, "Get not implemented");
    assert (false);
    return 0;
}

//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking get interface method.
 *  This method calls the corresponding BpConnect class method which 
 *  spawns a thread (forks off a process) that can block through 
 *  a framework adapter. When the process terminates the provider adapter
 *  invokes bp_notify_end_task() and notifies the producer adapter that the 
 *  method completed.
 * 
 *  @param framework_id    - Unique ID of the framework adapter
 *  @param producer_id     - Connection ID on the producer's framework adapter side
 *  @param call_id         - Unique ID, assigned to this call by the producer framework adapter
 *  @param stream_size_ptr - size (in words) of the returned serialized transaction 
 *                           data stream. The size value can be returned by this 
 *                           method only if the provider's get() implementation 
 *                           method returns immediately, without blocking
 *  @param stream          - container for returned serialized transaction data stream. 
 *                           It can be filled in this method only if the provider's 
 *                           get() implementation method returns immediately, 
 *                           without blocking
 *  @param done            - an output parameter; The provider adapter shall assign it 
 *                           true if the call was completed immediately (did not block)
 *  @param time_unit       - Current simulation time unit
 *  @param time_value      - Current simulatin time scaled according to time_unit
 * 
 *  @return Return status :
 *          - 0 - if the blocking calls completes normally
 *          - 1 - if the corresponding thread was disabled before normal completion
 * 
 */
int bp_request_get(int                framework_id,
                   int                producer_id,
                   int                call_id,
                   unsigned int *     stream_size_ptr,
                   uvm_ml_stream_t    stream,
                   unsigned int *     done,
                   uvm_ml_time_unit * time_unit,
                   double           * time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_request_get()\n");
    bool done_tmp = false;
    int result = BpInterconnect::RequestGet(framework_id, producer_id, call_id, *stream_size_ptr, stream, done_tmp, *time_unit, *time_value);
    *done = done_tmp;
    return result;
}

//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking get interface method.
 *  This method shall be invoked by the producer framework's ML 
 *  adapter after the thread spawned by RequestGet() completes and the 
 *  provider framework ML adapter notifies the producer via NotifyEndTask()
 * 
 *  @param framework_id    - Unique ID of the framework adapter
 *  @param producer_id     - Connection ID on the producer's framework adapter side
 *  @param call_id         - Unique ID, assigned to this call by the producer framework adapter
 *  @param stream          - container for returned serialized transaction data
 *                           stream. It can be filled in this method only if the 
 *                           provider's get() implementation method returns 
 *                           immediately, without blocking
 * 
 *  @return Output stream size.
 * 
 */
unsigned int bp_get_requested(int             framework_id,
			      int             producer_id,
			      int             call_id,
			      uvm_ml_stream_t stream)
{ 
    bp_printf(BP_DEBUG, "In bp_get_requested()\n");
    return BpInterconnect::GetRequested(framework_id, producer_id, call_id, stream);
}



//******************************************************************************
// ----- TLM1 transport API
//******************************************************************************


//------------------------------------------------------------------------------
//! TLM1 non-blocking transport interface method.
/*!
 *  @param framework_id         - Unique ID of the framework adapter
 *  @param producer_id          - Connection ID on the producer's framework adapter side
 *  @param req_stream_size      - Size (in words) of the serialized request data stream
 *  @param req_stream           - Serialize request data
 *  @param rsp_stream_size_ptr  - Size (in words) of the serialized response data stream
 *  @param rsp_stream           - Serialize response data
 *  @param time_unit            - Current simulation time unit
 *  @param time_value           - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 * 
 */
int bp_nb_transport(int               framework_id, 
                    int               producer_id, 
                    unsigned int      req_stream_size, 
                    uvm_ml_stream_t   req_stream,
                    unsigned int    * rsp_stream_size_ptr, 
                    uvm_ml_stream_t   rsp_stream,
                    uvm_ml_time_unit  time_unit,
                    double            time_value)
{ 
    bp_printf(BP_DEBUG, "In bp_nb_transport()\n");
    return BpInterconnect::NbTransportTLM1(framework_id, producer_id, req_stream_size, req_stream, *rsp_stream_size_ptr, rsp_stream, time_unit, time_value);
}

//------------------------------------------------------------------------------
//! TLM1 blocking transport interface method.
/*! This native blocking call is not supported.
 *  The pseudo-blocking mechanism of RequestTransport/NotifyEndTask() 
 *  should be used instead.
 * 
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param producer_id      - Connection ID on the producer's framework adapter side
 *  @param req_stream_size  - Size (in words) of the serialized request data stream
 *  @param req_stream       - Serialize request data
 *  @param rsp_stream_size  - Size (in words) of the serialized response data stream
 *  @param rsp_stream       - Serialize response data
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Returns 0 - unsupported.
 * 
 */
int bp_transport(int                framework_id, 
                 int                producer_id,
                 unsigned int       req_stream_size, 
                 uvm_ml_stream_t    req_stream,
                 unsigned int     * rsp_stream_size, 
                 uvm_ml_stream_t    rsp_stream,
                 uvm_ml_time_unit * time_unit,
                 double           * time_value)
{ 
    bp_printf(BP_DEBUG, "In bp_transport()\n");
    bp_printf(BP_ERROR, "Transport not implemented");
    assert (false);
    return 0;
}

//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking transport interface method. 
 *  This method calls the corresponding BpConnect class method which 
 *  spawns a thread (forks off a process) that can block through 
 *  a framework adapter. When the process terminates the provider adapter
 *  invokes bp_notify_end_task() and notifies the producer adapter that the 
 *  method completed.
 * 
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param producer_id      - Connection ID on the producer's framework adapter side
 *  @param call_id          - Unique ID, assigned to this call by the producer framework adapter
 *  @param req_stream_size  - Size (in words) of the serialized request data stream
 *  @param req_stream       - Serialize request data
 *  @param rsp_stream_size  - Size (in words) of the serialized response data stream
 *  @param rsp_stream       - Serialize response data
 *  @param done             - An output parameter; The provider adapter shall assign it 
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Return status :
 *          - 0 - if the blocking calls completes normally
 *          - 1 - if the corresponding thread was disabled before normal completion
 */
int bp_request_transport(int                framework_id, 
                         int                producer_id,
                         int                call_id,
                         unsigned int       req_stream_size, 
                         uvm_ml_stream_t    req_stream,
                         unsigned int *     rsp_stream_size, 
                         uvm_ml_stream_t    rsp_stream,
                         unsigned int *     done,
                         uvm_ml_time_unit * time_unit,
                         double           * time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_request_transport()\n");
    bool done_tmp = false;
    int result = BpInterconnect::RequestTransportTLM1(framework_id, producer_id, call_id, req_stream_size, req_stream, *rsp_stream_size, rsp_stream, done_tmp, *time_unit, *time_value);
    *done = done_tmp;
    return result;
} 


//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking transport interface method.
 *  This method shall be invoked by the producer framework's ML 
 *  adapter after the thread spawned by RequestTransport() completes and the 
 *  provider framework ML adapter notifies the producer via NotifyEndTask()
 * 
 *  @param framework_id    - Unique ID of the framework adapter
 *  @param producer_id     - Connection ID on the producer's framework adapter side
 *  @param call_id         - Unique ID, assigned to this call by the producer framework adapter
 *  @param rsp_stream      - Serialize data
 * 
 *  @return Output stream size.
 */
unsigned int bp_transport_response(int              framework_id, 
                                   int              producer_id,
                                   int              call_id,
                                   uvm_ml_stream_t  rsp_stream) 
{ 
    bp_printf(BP_DEBUG, "In bp_transport_response()\n");
    return BpInterconnect::TransportTLM1Response(framework_id, producer_id, call_id, rsp_stream);
}


//******************************************************************************
// ----- Analysis API
//******************************************************************************

//------------------------------------------------------------------------------
//! Analysis write interface method.
/*!
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param stream_size  - Size (in words) of the serialized data stream
 *  @param stream       - Serialize data
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 * 
 */
void bp_write(int              framework_id, 
              int              producer_id, 
              unsigned int     stream_size, 
              uvm_ml_stream_t  stream,
              uvm_ml_time_unit time_unit,
              double           time_value)
{ 
    bp_printf(BP_DEBUG, "In bp_write()\n");
    BpInterconnect::Write(framework_id, producer_id, stream_size, stream, time_unit, time_value);
}



//******************************************************************************
// ----- TLM1 peek API
//******************************************************************************

//------------------------------------------------------------------------------
//! TLM1 non-blocking peek interface method.
/*!
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param producer_id      - Connection ID on the producer's framework adapter side
 *  @param stream_size_ptr  - Return value : Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 */
int bp_nb_peek(int              framework_id,
               int              producer_id,
               unsigned int *   stream_size_ptr,
               uvm_ml_stream_t  stream,
               uvm_ml_time_unit time_unit,
               double           time_value) 
{
    bp_printf(BP_DEBUG, "In bp_nb_peek()\n");
    return BpInterconnect::NbPeek(framework_id, producer_id, *stream_size_ptr, stream, time_unit, time_value);
}


//------------------------------------------------------------------------------
//! TLM1 can_peek interface.
/*!
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param producer_id      - Connection ID on the producer's framework adapter side
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the export
 */
int bp_can_peek(int              framework_id,
                int              producer_id,  
                uvm_ml_time_unit time_unit,
                double           time_value) 
{
    bp_printf(BP_DEBUG, "In bp_can_peek()\n");
    return BpInterconnect::CanPeek(framework_id, producer_id, time_unit, time_value);
}

//------------------------------------------------------------------------------
//! TLM1 blocking peek interface method.
/*! This native blocking call is not supported.
 *  The pseudo-blocking mechanism of bp_request_peek()/bp_notify_end_task()
 *  should be used instead.
 * 
 *  @param framework_id - Unique ID of the framework adapter
 *  @param producer_id  - Connection ID on the producer's framework adapter side
 *  @param stream       - Serialize data
 *  @param time_unit    - Current simulation time unit
 *  @param time_value   - Current simulatin time scaled according to time_unit
 * 
 *  @return Returns 0 - unsupported.
 */
unsigned int bp_peek(int                framework_id,
                     int                producer_id,
                     uvm_ml_stream_t    stream,
                     uvm_ml_time_unit * time_unit,
                     double           * time_value)
{
    bp_printf(BP_DEBUG, "In bp_peek()\n");
    bp_printf(BP_ERROR, "Peek not implemented");
    assert(false);
    return 0;
}


//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking peek interface method.
 *  This method spawns a thread (forks off a process) that can block through 
 *  a framework adapter. When the process terminates the provider adapter
 *  invokes NotifyEndTask() and notifies the producer adapter that the 
 *  method completed.
 * 
 *  @param framework_id    - Unique ID of the framework adapter
 *  @param producer_id     - Connection ID on the producer's framework adapter side
 *  @param call_id         - Unique ID, assigned to this call by the producer framework adapter
 *  @param stream_size_ptr - Size (in words) of the serialized data stream
 *  @param stream          - Serialize data
 *  @param done            - an output parameter; The provider adapter shall assign it 
 *                           true if the call was completed immediately (did not block)
 *  @param time_unit       - Current simulation time unit
 *  @param time_value      - Current simulatin time scaled according to time_unit
 * 
 *  @return Return status :
 *          - 0 - if the blocking calls completes normally
 *          - 1 - if the corresponding thread was disabled before normal completion
 */
int bp_request_peek(int                framework_id, 
                    int                producer_id,
                    int                call_id,
                    unsigned int     * stream_size_ptr,
                    uvm_ml_stream_t    stream,
                    unsigned *         done,
                    uvm_ml_time_unit * time_unit,
                    double           * time_value) 
{ 
    bp_printf(BP_DEBUG, "In bp_request_peek()\n");
    bool done_tmp = false;
    int result = BpInterconnect::RequestPeek(framework_id, producer_id, call_id, *stream_size_ptr, stream, done_tmp, *time_unit, *time_value);
    *done = done_tmp;
    return result;
}


//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM1 blocking peek interface method.
 *  This method shall be invoked by the producer framework's ML 
 *  adapter after the thread spawned by RequestPeek() completes and the 
 *  provider framework ML adapter notifies the producer via NotifyEndTask()
 * 
 *  @param framework_id    - Unique ID of the framework adapter
 *  @param producer_id     - Connection ID on the producer's framework adapter side
 *  @param call_id         - Unique ID, assigned to this call by the producer framework adapter
 *  @param stream          - Serialize data
 * 
 *  @return Output stream size.
 */
unsigned int bp_peek_requested(int              framework_id,
                               int              producer_id,
                               int              call_id, 
                               uvm_ml_stream_t  stream)
{
    bp_printf(BP_DEBUG, "In bp_peek_requested()\n");
    return BpInterconnect::PeekRequested(framework_id, producer_id, call_id, stream);
}



//******************************************************************************
// ----- TLM2 API
//******************************************************************************

//------------------------------------------------------------------------------
//! TLM2 blocking transport method.
/*! This native blocking call is not supported.
 *  The pseudo-blocking mechanism of bp_request_b_transport_tlm2()/NotifyEndTask() 
 *  should be used instead.
 * 
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param initiator_id     - Connection ID on the initiator's framework adapter side
 *  @param stream_size      - Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param delay_unit       - Delay time unit
 *  @param delay_value      - Delay time scaled according to delay_unit
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Returns 0, unsupported.
 */
int bp_b_transport_tlm2(int                framework_id, 
                        int                initiator_id, 
                        unsigned int     * stream_size,
                        uvm_ml_stream_t  * stream,
                        uvm_ml_time_unit * delay_unit,
                        double           * delay_value,
                        uvm_ml_time_unit   time_unit,
                        double             time_value)

{
  bp_printf(BP_DEBUG,"In bp_b_transport_tlm2()\n");
  bp_printf(BP_ERROR, "b_transport not implemented");
  assert (false);
  return 0;
}
 

//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM2 blocking transport interface method.
 *  This method spawns a thread (forks off a process) that can block through 
 *  a framework adapter. When the process terminates the provider adapter
 *  invokes NotifyEndTask() and notifies the producer adapter that the 
 *  method completed.
 * 
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param initiator_id     - Connection ID on the initiator's framework adapter side
 *  @param call_id          - Unique ID, assigned to this call by the initiator's framework adapter
 *  @param stream_size      - Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param delay_unit       - Delay time unit
 *  @param delay_value      - Delay time scaled according to delay_unit
 *  @param done             - An output parameter; The provider adapter shall assign it 
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Return status :
 *          - 0 - if the blocking calls completes normally
 *          - 1 - if the corresponding thread was disabled before normal completion
 */
int bp_request_b_transport_tlm2(int               framework_id, 
                                int               initiator_id, 
                                int               call_id,
                                unsigned int *    stream_size,
                                uvm_ml_stream_t * stream,
                                uvm_ml_time_unit  delay_unit,
                                double            delay_value,
                                unsigned int *    done, 
                                uvm_ml_time_unit  time_unit, 
                                double            time_value)
{
  bp_printf(BP_DEBUG,"In bp_request_b_transport_tlm2()\n");

  uvm_ml_time delay;
  delay.units = delay_unit;
  delay.value = delay_value;

  bool done_tmp = false;
  int result = BpInterconnect::RequestBTransportTLM2(framework_id,initiator_id,call_id,*stream_size,*stream,delay,done_tmp,time_unit,time_value);
  *done = done_tmp;
  return result;
}
 
//------------------------------------------------------------------------------
//! Part of the pseudo-blocking mechanism for implementation of the 
/*! TLM2 blocking transport interface method.
 *  This method shall be invoked by the producer framework's ML 
 *  adapter after the thread spawned by bp_request_b_transport_tlm2() completes and the 
 *  provider framework ML adapter notifies the producer via NotifyEndTask()
 * 
 *  @param framework_id    - Unique ID of the framework adapter
 *  @param initiator_id    - Connection ID on the initiator's framework adapter side
 *  @param call_id         - Unique ID, assigned to this call by the initiator framework adapter
 *  @param stream_size     - Size (in words) of the serialized response data stream
 *  @param stream          - Serialize data
 * 
 *  @return Value returned by the target
 */
int bp_b_transport_tlm2_response(int             framework_id, 
                                 int             initiator_id, 
                                 int             call_id,
                                 unsigned int *  stream_size,
                                 uvm_ml_stream_t stream)
{
  bp_printf(BP_DEBUG,"In bp_b_transport_tlm2_response()\n");
  return BpInterconnect::BTransportTLM2Response(framework_id,initiator_id,call_id,*stream_size,stream);
}

//------------------------------------------------------------------------------
//! TLM2 non-blocking FW transport interface method.
/*!
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param initiator_id     - Connection ID on the initiator's framework adapter side
 *  @param stream_size      - Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param phase            - TLM2 timing points (BEGIN_REQ, END_REQ ...)
 *  @param transaction_id   - ID of for this transaction
 *  @param delay_unit       - Delay time unit
 *  @param delay_value      - Delay time scaled according to delay_unit
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return tlm_sync_enum value returned by target
 */
uvm_ml_tlm_sync_enum bp_nb_transport_fw(int                framework_id, 
                                        int                initiator_id,
                                        unsigned int *     stream_size,
                                        uvm_ml_stream_t *  stream,
                                        uvm_ml_tlm_phase * phase,
                                        unsigned int       transaction_id,
                                        uvm_ml_time_unit * delay_unit,
                                        double *           delay_value, 
                                        uvm_ml_time_unit   time_unit, 
                                        double             time_value)
{
  bp_printf(BP_DEBUG,"In bp_nb_transport_fw()\n");

  uvm_ml_time delay;
  delay.units = *delay_unit;
  delay.value = *delay_value;

  uvm_ml_tlm_sync_enum result = BpInterconnect::NbTransportFwTLM2(framework_id,initiator_id,*stream_size,*stream,*phase,transaction_id,delay,time_unit,time_value);

  *delay_unit = delay.units;
  *delay_value = delay.value;

  return result;
}

//------------------------------------------------------------------------------
//! TLM2 non-blocking BW transport interface method.
/*!
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param target_id        - Connection ID on the target's framework adapter side
 *  @param stream_size      - Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param phase            - TLM2 timing points (BEGIN_REQ, END_REQ ...)
 *  @param transaction_id   - ID of for this transaction
 *  @param delay_unit       - Delay time unit
 *  @param delay_value      - Delay time scaled according to delay_unit
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return tlm_sync_enum value returned by initiator
 */
uvm_ml_tlm_sync_enum bp_nb_transport_bw(int                framework_id, 
                                        int                target_id,
                                        unsigned int *     stream_size,
                                        uvm_ml_stream_t *  stream,
                                        uvm_ml_tlm_phase * phase,
                                        unsigned int       transaction_id,
                                        uvm_ml_time_unit * delay_unit,
                                        double *           delay_value, 
                                        uvm_ml_time_unit   time_unit, 
                                        double             time_value)
{
  bp_printf(BP_DEBUG,"In bp_nb_transport_bw()\n");

  uvm_ml_time delay;
  delay.units = *delay_unit;
  delay.value = *delay_value;

  uvm_ml_tlm_sync_enum result = BpInterconnect::NbTransportBwTLM2(framework_id,target_id,*stream_size,*stream,*phase,transaction_id,delay,time_unit,time_value);

  *delay_unit = delay.units;
  *delay_value = delay.value;

  return result;
}


//------------------------------------------------------------------------------
//! TLM2 transport debug interface method.
/*!
 * 
 *  @param framework_id     - Unique ID of the framework adapter
 *  @param initiator_id     - Connection ID on the initiator's framework adapter side
 *  @param stream_size      - Size (in words) of the serialized data stream
 *  @param stream           - Serialize data
 *  @param time_unit        - Current simulation time unit
 *  @param time_value       - Current simulatin time scaled according to time_unit
 * 
 *  @return Value returned by the target
 */
unsigned int bp_transport_dbg(int               framework_id, 
                              int               initiator_id,
                              unsigned int *    stream_size,
                              uvm_ml_stream_t * stream, 
                              uvm_ml_time_unit  time_unit, 
                              double            time_value)
{
  bp_printf(BP_DEBUG,"In bp_transport_dbg()\n");
  return BpInterconnect::TransportDbgTLM2(framework_id,initiator_id,*stream_size,*stream,time_unit,time_value);
}

//------------------------------------------------------------------------------
//! Return a transaction ID to the framework.
/*!
 *  @param framework_id - Unique ID of the framework adapter
 * 
 *  @return Returns a unique transaction ID.
 */
unsigned int bp_assign_transaction_id(int framework_id)
{
  bp_printf(BP_DEBUG,"In bp_assign_transaction_id()\n");
  return BpInterconnect::AssignTransactionId(framework_id);
}

//------------------------------------------------------------------------------
//! TLM2 transaction mapping.
/*!
 *  @param framework_id - Unique ID of the framework adapter
 *  @param socket_name  - Name of the socket
 */
void bp_turn_off_transaction_mapping(int framework_id, const char *socket_name)
{
  bp_printf(BP_DEBUG, 
		  "UVM-ML BP>> In bp_turn_off_transaction_mapping() called by framework %d.\n", framework_id);

  string socketName = socket_name;
  BpInterconnect::TurnOffTransactionMapping(framework_id, socketName);
}

//******************************************************************************
// ----- ML Hierarchical Consruction API
//******************************************************************************

//------------------------------------------------------------------------------
//! Create a child junction node.
/*!
 *  @param framework_id               - Unique ID of the framework adapter
 *  @param target_framework_indicator - Target framework's indicator name 
 *  @param component_type_name        - Component type name of the child to be created
 *  @param instance_name              - Instance name of the child to be created
 *  @param parent_full_name           - Full hierarchical path name of the calling parent component
 *  @param parent_junction_node_id    - ID of the parent junction node
 *  
 *  @return  <0 : error
 */
int bp_create_child_junction_node(int            framework_id,
                                  const char *   target_framework_indicator,
                                  const char *   component_type_name,
                                  const char *   instance_name,
                                  const char *   parent_full_name,
                                  int            parent_junction_node_id)
{
  bp_printf(BP_DEBUG, "In bp_create_child_junction_node()\n");
  return BpInterconnect::CreateChildJunctionNode(framework_id,
                                                 string(target_framework_indicator),
                                                 string(component_type_name),
                                                 string(instance_name),
                                                 string(parent_full_name),
                                                 parent_junction_node_id);

}


//******************************************************************************
// ----- Type identification and mapping API
//******************************************************************************

//------------------------------------------------------------------------------
//! Returns the type ID of a transaction by it's name.
/*! May be used for transaction runtime type identification
 *  Assuming that the connected frameworks support passing polymorphic transactions
 *  across the same TLM port/socket, the connected frameworks shall map the corresponding
 *  type names and obtain the unique type id from the bp. By default, the
 *  corresponding types are matched by name. Once the type id is obtained, 
 *  it shall be included by the producer/initiator in the transaction meta data 
 *  and the provider/target shall use the id to construct the correct object.
 * 
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param type_name     - Type name of a transaction object
 * 
 *  @return Transaction object type ID.
 */
uvm_ml_type_id_t bp_get_type_id_from_name(int framework_id, const char* type_name) 
{ 
    uvm_ml_type_id_t result = BpInterconnect::GetTypeIdByTypeName(framework_id,string(type_name));
    bp_printf(BP_DEBUG, 
            "In bp_get_type_id_from_name() called by framework %d for type name %s. Returned id is %d\n", framework_id, type_name, (int) result);
    return result;
}

//------------------------------------------------------------------------------
//! Returns the transaction type name given the type ID.
/*! May be used by a framework if it supports passing polymorphic
 *  transactions and needs a class name in order to construct the corresponding object
 *  on the provider/target side.
 * 
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param type_id       - Type ID for transaction object
 * 
 *  @return Returns transaction object type name.
 */
char* bp_get_type_name_from_id(int framework_id, uvm_ml_type_id_t type_id) 
{ 
    char * result = const_cast<char *> (BpInterconnect::GetTypeNameByTypeId(framework_id,type_id,true).c_str());
    bp_printf(BP_DEBUG, 
            "In bp_get_type_name_from_id() called by framework %d for type id %d. Returned type name is %s\n", framework_id, type_id, result);
    return result;
}

//------------------------------------------------------------------------------
//! Allows explicit type mapping.  Default mapping is by the exact
/*! type names match.
 *  
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param type1         - Type name 1
 *  @param type2         - Type name 2
 * 
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
int bp_set_match_types(int framework_id, const char* type1, const char* type2) {
    bp_printf(BP_DEBUG,
		    "In bp_set_match_types() called by framework %d with type1 = %s type2 = %s\n",framework_id,type1,type2);
    
    string frameworkIndicator1, frameworkIndicator2, typeName1, typeName2;

    BpInterconnect::ParseTypeName(string(type1), frameworkIndicator1, typeName1);
    BpInterconnect::ParseTypeName(string(type2), frameworkIndicator2, typeName2);
    BpLangTypeName bpType1 (frameworkIndicator1, typeName1);
    BpLangTypeName bpType2 (frameworkIndicator2, typeName2);

    bool res = BpInterconnect::RegisterTypeMatch(bpType1, bpType2); 
    // false can be returned in a potentiaally legal scenario if the frameworks is not currently used
    return (res == true ? 1 : 0);
}


//******************************************************************************
// ----- Max Pack Size API
//******************************************************************************

/* =================================================
   M A X   P A C K   S I Z E   A P I // Legacy
   ================================================= */
int bp_pack_max_size = -1;

//------------------------------------------------------------------------------
//! Get the maximum size of data packing from target framework
/*!
 *  @param framework_id - unique id of the target framework
 *
 *  @return max size value returned from framework
 */
int bp_get_pack_max_size(int framework_id)
{
    bp_printf(BP_DEBUG, "In bp_get_pack_max_size()\n");
    return bp_pack_max_size;
}

//------------------------------------------------------------------------------
//! Set the maximum size of data packing in target framework
/*!
 *  @param framework_id - unique id of the target framework
 *  @param size         - max size value
 *
 *  @return void
 */
void bp_set_pack_max_size(int framework_id,int size)
{
    bp_printf(BP_DEBUG, 
            "In bp_set_pack_max_size() called by framework %d. New size is %d\n", framework_id, size);
    bp_pack_max_size = size;
}


//******************************************************************************
// ---- Service API
//******************************************************************************

//------------------------------------------------------------------------------
//! Register service providers with the backplane.
/*! Indicates to the backplane which services are being provided by
 *  which framework.  Could be call from the framework or the
 *  the user TB code.  All srv variables need not be filled.  Empty
 *  strings will be ignored.  If the same service is set multiple
 *  times, the last setting will be used.
 * 
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param srv_providers - A struct containing variables
 *                         of type char * of all available 
 *                         services. Each variable 
 *                         specifies the name of the 
 *                         framework providing that service.
 */
void bp_register_srv_providers (
    unsigned int            framework_id,
    bp_srv_provider_struct *srv_providers)
{
    bp_printf(BP_DEBUG, "In bp_register_srv_provider()\n");
    BpInterconnect::RegisterSrvProviders(framework_id, srv_providers);
}


//******************************************************************************
// ----- Phasing API
//******************************************************************************

//------------------------------------------------------------------------------
//! Notifies non-runtime phase (pre/post run phases, phase start, 
/*! phase ready to end and phase ended notifications for all phases
 *  including runtime phases).
 * 
 *  Called by the master phase controller to notify a phase has started,
 *  is ready to end or has ended. Pre-run and post-run
 *  phases could be executed topdown (from parent to child) or bottom-up
 *  (from child to parent). 
 * 
 *  @param framework_id  - In the case of broadcasting, it's the unique ID 
 *                         of the master phase controller's framework adapter.
 *                         In the case where the notification is to a
 *                         particular component (target_id >= 0), it's 
 *                         the framework ID of the target component.
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param phase_action  - The action for this phase (start, execute,
 *                         ready to end, ended)
 * 
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
int bp_notify_phase (
    unsigned int        framework_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action)
{
    int result;

    bp_printf(BP_DEBUG, "In bp_notify_phase()\n");
    result = BpInterconnect::NotifyPhase(framework_id, phase_group, phase_name, phase_action);
    return result;
}


//------------------------------------------------------------------------------
//! Notifies a component of a non-time consuming phase.
/*!
 *  Called by a child proxy to notify a parent proxy of a phase. For 
 *  unified hierachy, the child proxy node will transmit all its non-time 
 *  consuming phase notifications to all connected parent proxies.
 * 
 *  @param framework_id    - In the case of broadcasting, it's the unique ID 
 *                           of the master phase controller's framework adapter.
 *                           In the case where the notification is to a
 *                           particular component (target_id >= 0), it's 
 *                           the framework ID of the target component.
 *  @param target_frmw_ind - Framework indicator for the target
 *  @param target_id       - The ID of the target.
 *  @param phase_group     - Name of the group the phase belongs in 
 *                           (eg. common, uvm ...)
 *  @param phase_name      - Name of the phase
 *  @param phase_action    - The action for this phase (start, execute,
 *                           ready to end, ended)
 * 
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
int bp_transmit_phase (
    unsigned int        framework_id,
    const char *        target_frmw_ind,
    int                 target_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action)
{

    int result;

    bp_printf(BP_DEBUG, "In bp_transmit_phase()\n");
    result = BpInterconnect::TransmitPhase(framework_id, string(target_frmw_ind), target_id, 
                                           phase_group, phase_name, phase_action);
    return result;
}

//------------------------------------------------------------------------------
//! Notifies the execution of a runtime phase.  A phase that consumes time.
/*!
 *  Called by the master phase controller to notify a runtime phase.
 *  Unlike non-runtime phases which could execute either 
 *  topdown or bottom-up, a runtime phase is executed 'in parallel'.  
 *  Therefore, the phase is broadcast to all framework only once,
 *  regardless of how many toplevel components the framework contains.
 *  The framework should phase all its' toplevel component at the same time.
 *  A framework could choose to participate in phase synchronization
 *  (controlling when the phase will end) by asserting the participate 
 *  variable.  The framework notifies the phase master that it's 
 *  ready to exit the phase by calling bp_notify_phase_done().  The 
 *  master phase controller will wait until all participating frameworks
 *  are ready to exit the phase before continuing on to the next phase. 
 * 
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param phase_action  - The action for this phase (start, execute,
 *                         ready to end, ended)
 *  @param time_unit     - Current simulation time unit
 *  @param time_value    - Current simulatin time scaled according to time_unit
 *  @param participate   - Indicate the number of frameworks participating in this phase
 * 
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
void bp_notify_runtime_phase (
    unsigned int        framework_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action,
    uvm_ml_time_unit    time_unit,
    double              time_value,
    unsigned int *      participate)
{

    bp_printf(BP_DEBUG, "In bp_notify_runtime_phase()\n");
    BpInterconnect::NotifyRuntimePhase(framework_id, phase_group, phase_name, phase_action, (uvm_ml_time_unit) time_unit, time_value, participate);
}

//------------------------------------------------------------------------------
//! Notifies the phase controller that this frameowork is ready to exit this phase.
/*!
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param time_unit     - Current simulation time unit
 *  @param time_value    - Current simulatin time scaled according to time_unit
 */
void bp_notify_phase_done (
    unsigned int      framework_id,
    const char *      phase_group,
    const char *      phase_name,
    uvm_ml_time_unit  time_unit,
    double            time_value)
{
    bp_printf(BP_DEBUG, "In bp_notify_phase_done()\n");
    BpInterconnect::PhaseSrvNotifyPhaseDone(framework_id, phase_group, phase_name, time_unit, time_value);
}


/// @cond PRIVATE
//------------------------------------------------------------------------------
//
// 
unsigned int bp_in_ml_ovm_mode() 
{ 
    return 0;
} 

//------------------------------------------------------------------------------
//
// 
unsigned int bp_in_ml_uvm_mode() 
{   
    return 1;
} 
/// @endcond


///////////////////////////////////////////////////////////////////////
/// Broadcast notification about a resource value set
/// Indicates to the backplane that a resource scope, name, value
/// and the operation kind (action) should be transmitted to all involved 
/// frameworks.
/// @param framework_id  - Unique ID of the framework adapter
/// @param action - an enumeration indicating a resource setting operation
/// @param item_scope - hierarchical scope for the notified resource
/// @param item_name - name of the resource item
/// @param accessor_name - full name of the context where the resource was set
/// @stream_size - size of the message stream
/// @stream - the message stream; may represent a packed typed object, an untyped raw stream (for integral values) or a stirng
/// @param time_unit     - Current simulation time unit
/// @param time_value    - Current simulatin time scaled according to time_unit
///////////////////////////////////////////////////////////////////////
int bp_notify_resource (
    int                           framework_id,
    uvm_ml_resource_notify_action action,
    const char *                  item_scope,
    const char *                  item_name,
    const char *                  accessor_name,
    unsigned int                  stream_size,
    uvm_ml_stream_t               stream,
    uvm_ml_time_unit              time_unit, 
    double                        time_value)
{
    bp_printf(BP_DEBUG, "UVM-ML BP>> In bp_notify_resource() with\n");
    bp_printf(BP_DEBUG, "            item_scope = %s item_name = %s\n", item_scope, item_name);
    bp_printf(BP_DEBUG, "            action = %d stream_size = %d\n", action, stream_size);
    bp_printf(BP_DEBUG, "            stream kind = %d accessor_name = %s\n", *(int *)stream, accessor_name);
    bp_printf(BP_DEBUG, "\n");

    return 1;
}

///////////////////////////////////////////////////////////////////////
/// Broadcast notification about a configuration element set
/// Indicates to the backplane that a context, instance name,
/// field name and value should be transmitted to all involved frameworks
/// @param framework_id  - Unique ID of the framework adapter
/// @param cntxt - full hierarchical name of a quasi-static component where the configuration was set
/// @param instance_name - instance name of the quasi-static component being configured
/// @param field_name - name of the field being configured
/// @stream_size - size of the message stream
/// @stream - the message stream; may represent a packed typed object, an untyped raw stream (for integral values) or a stirng
/// @param time_unit     - Current simulation time unit
/// @param time_value    - Current simulatin time scaled according to time_unit
///////////////////////////////////////////////////////////////////////
void bp_notify_config (
    int              framework_id,
    const char *     cntxt,
    const char *     instance_name,
    const char *     field_name,
    unsigned int     stream_size,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit, 
    double           time_value)
{
    bp_printf(BP_DEBUG, "UVM-ML BP>> In bp_notify_config() with \n");
    bp_printf(BP_DEBUG, "            context = %s instance_name = %s field_name = %s\n", cntxt, instance_name, field_name);
    bp_printf(BP_DEBUG, "            stream_size = %d \n", stream_size);
    bp_printf(BP_DEBUG, "            stream kind = %d\n", *(int *)stream);
    bp_printf(BP_DEBUG, "\n");

    BpInterconnect::NotifyConfig(framework_id, cntxt, instance_name, field_name, stream_size, stream, time_unit, time_value);
}

}   // extern 'C'



////////////////////////////////////////////////////////////////////////////////

//! Macro that sets the function ptr in the C API tray
#define SET_TRAY_ITEM(i) m_c_api_tray.i##_ptr = bp_##i

//------------------------------------------------------------------------------
//! Fill the BP provided API tray with extern 'C' function pointers.
//
void BpInterconnect::fillCApiTray() 
{
  SET_TRAY_ITEM(set_trace_mode);
  SET_TRAY_ITEM(register_framework); 
  SET_TRAY_ITEM(get_version);
  SET_TRAY_ITEM(add_root_node);
  SET_TRAY_ITEM(run_test);
  SET_TRAY_ITEM(connect);
  SET_TRAY_ITEM(get_connector_size);

  SET_TRAY_ITEM(put);
  SET_TRAY_ITEM(nb_put);
  SET_TRAY_ITEM(can_put);
  SET_TRAY_ITEM(notify_end_blocking);
  SET_TRAY_ITEM(get);
  SET_TRAY_ITEM(nb_get);
  SET_TRAY_ITEM(can_get);
  SET_TRAY_ITEM(transport);
  SET_TRAY_ITEM(nb_transport);
  SET_TRAY_ITEM(write);
  SET_TRAY_ITEM(request_put);
  SET_TRAY_ITEM(request_get);
  SET_TRAY_ITEM(get_requested);
  SET_TRAY_ITEM(peek);
  SET_TRAY_ITEM(request_peek);
  SET_TRAY_ITEM(peek_requested);
  SET_TRAY_ITEM(nb_peek);
  SET_TRAY_ITEM(can_peek);
  SET_TRAY_ITEM(request_transport);
  SET_TRAY_ITEM(transport_response);
  
  SET_TRAY_ITEM(b_transport_tlm2);
  SET_TRAY_ITEM(request_b_transport_tlm2);
  SET_TRAY_ITEM(b_transport_tlm2_response);
  SET_TRAY_ITEM(nb_transport_fw);
  SET_TRAY_ITEM(nb_transport_bw);
  SET_TRAY_ITEM(transport_dbg);
  SET_TRAY_ITEM(assign_transaction_id);
  SET_TRAY_ITEM(turn_off_transaction_mapping);
  SET_TRAY_ITEM(synchronize);
  
  SET_TRAY_ITEM(get_type_id_from_name);
  SET_TRAY_ITEM(get_type_name_from_id);
  SET_TRAY_ITEM(set_match_types);

  SET_TRAY_ITEM(create_child_junction_node);
    
  SET_TRAY_ITEM(reset);  

  SET_TRAY_ITEM(notify_phase);  
  SET_TRAY_ITEM(transmit_phase);  
  SET_TRAY_ITEM(notify_runtime_phase);  
  SET_TRAY_ITEM(notify_phase_done);
  SET_TRAY_ITEM(register_srv_providers);

  SET_TRAY_ITEM(get_pack_max_size);
  SET_TRAY_ITEM(set_pack_max_size);
  SET_TRAY_ITEM(notify_resource);
  SET_TRAY_ITEM(notify_config);
}

//------------------------------------------------------------------------------
//! Returns a pointer to the BP provided API function pointer tray.
/*! When called for the very first time it fills the function tray
 *  and returns it.
 */
bp_api_struct * BpInterconnect::GetProvidedTray()
{
    static bool ready = false;
    if (!ready) {
      fillCApiTray();
      ready = true;    
    }
    return &m_c_api_tray;
}

///   @}   // end of BP_Provided group

