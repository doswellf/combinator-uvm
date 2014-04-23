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

#ifndef BP_PROVIDED_H
#define BP_PROVIDED_H

#include "bp_common_c.h"
#include "bp_required.h"


/*! @file bp_provided.h
 *  @mainpage Backplane provided C API
 *
 *  @section API Backplane provided C API
 *  This API defines the services supported by the backplane.
 * 
 *  @defgroup BP_Provided Backplane provided API
 *  @{
 */

/* =====================================================
    B A C K P L A N E   P R O V I D E D   C  A P I
   ========== ========================================== */

//! Macro for backplane function type define
#define BP_PROVIDED_API_FUNCTION(f) bp_##f##_type f##_ptr

#ifdef __cplusplus
extern "C" {
#endif


//******************************************************************************
// -----  Backplane and frameworks setup API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_set_trace_mode() function ptr
/*! Set the trace mode
 *
 *  @param mode - 
 *
 *  @return void
 */
typedef void (*bp_set_trace_mode_type)
(
    int mode
);

//------------------------------------------------------------------------------
//! typedef for bp_register_framework() function ptr
/*! Register a framework
 *
 *  @param framework_name       - Unique name of the framework
 *  @param framework_indicators - Array of frame indicators
 *  @param framework_api        - Pointer to the API struct
 *
 *  @return unique ID assigned to this framework
 */
typedef int (*bp_register_framework_type)
(
   char *                 framework_name,
   char *                 framework_indicators [],
   bp_frmw_c_api_struct * framework_api
);

//------------------------------------------------------------------------------
//! typedef for bp_get_version() function ptr
/*! Obtain the backplane version
 *
 *  @return pointer to version string
 */
typedef char* (*bp_get_version_type) ();

//------------------------------------------------------------------------------
//! typedef for bp_add_root_node() function ptr
/*! Register a root node
 *
 *  @param framework_id   - unique id of the framework
 *  @param top_level_id   - unique id of the root node
 *  @param component_name - name of the root node
 *  @param instance_name  - instance name of the root node
 *
 *  @return unique id of the root node
 */
typedef int (*bp_add_root_node_type) 
(
    unsigned     framework_id, 
    unsigned     top_level_id, 
    const char * component_name,
    const char * instance_name
);

//------------------------------------------------------------------------------
//! typdef for bp_peek_uvm_ml_stream function ptr
/*! Start environment and run test.
 *
 *  @param framework_id - unique id of the framework
 *  @param tops_n       - number of top components
 *  @param tops         - list of names of the top components
 *  @param test         - name of the test component
 *
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
typedef int (*bp_run_test_type)
(
    int     framework_id,
    int     tops_n,
    char ** tops, 
    char *  test
);


//------------------------------------------------------------------------------
//! typedef for bp_reset() function ptr
/*! Broadcast RESET condition through backplane
 *
 *  @return void
 */
typedef void (*bp_reset_type)();


//******************************************************************************
// ---- Service API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_register_srv_providers() function ptr
/*! Called to backplane to register which framework will provide which service.
 *
 *  @param framework_id  - Framework ID of caller
 *  @param srv_providers - List of fields populated with the names of the 
 *                         framework providing the service. Not all fields
 *                         need to be populated.  Blank names will be ignored.
 */
typedef void (*bp_register_srv_providers_type)
(
    unsigned                 framework_id, 
    bp_srv_provider_struct * srv_providers
);


//******************************************************************************
// ----- Phasing API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_notify_phase() function ptr
/*! Notifies non-time consuming  phasea.
 *  Called by the master phase controller to notify a phase has started,
 *  is ready to end or has ended.
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
typedef int (*bp_notify_phase_type)
(
    unsigned int        framework_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action
);

//------------------------------------------------------------------------------
//! typedef for bp_transmit_phase() function ptr
/*! Notifies a component of a non-time consuming phase.
 *
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
typedef int (*bp_transmit_phase_type)
(
    unsigned int        framework_id,
    const char *        target_frmw_ind,
    int                 target_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action
);

//------------------------------------------------------------------------------
//! typedef for bp_notify_runtime_phase() function ptr
/*! Notifies the execution of a time consuming phase.
 * 
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
typedef void (*bp_notify_runtime_phase_type)
(
    unsigned int        framework_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action,
    uvm_ml_time_unit    time_unit,
    double              time_value,
    unsigned int *      participate
);

//------------------------------------------------------------------------------
//! typedef for bp_notify_phase_done() function ptr
/*! Notifies the phase controller that this frameowork is ready to exit this phase.
 * 
 *  @param framework_id  - Unique ID of the framework adapter
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param time_unit     - Current simulation time unit
 *  @param time_value    - Current simulatin time scaled according to time_unit
 */
typedef void (*bp_notify_phase_done_type)
(
    unsigned int      framework_id,
    const char *      phase_group,
    const char *      phase_name,
    uvm_ml_time_unit  time_unit,
    double            time_value
);



//******************************************************************************
// ----- TLM Common API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_connect() function ptr
/*! Register connection between initiator and target
 *
 *  @param framework_id - unique id of the framework
 *  @param path1        - full path of initiator
 *  @param path2        - full path of traget
 *
 *  @return status returned from target framework
 */
typedef unsigned (*bp_connect_type) 
(
    unsigned       framework_id,
    const char *   path1,
    const char *   path2
);

//------------------------------------------------------------------------------
//! typedef for bp_get_connector_size() function ptr
/*! Get the size of a connector from target framework
 *
 *  @param framework_id                               - unique id of the target framework
 *  @param connector_id                               - unique id of the connector
 *
 *  @return                               - the connector size
 */
typedef int (*bp_get_connector_size_type) 
(
    int framework_id, 
    int connector_id
);


//------------------------------------------------------------------------------
//! typedef for bp_notify_end_blocking() function ptr
/*! Part of the pseudo-blocking mechanism. When a blocking process terminates, 
 *  the provider adapter calls this method to notifies that the transaction has
 *  completed.
 * 
 *  @param framework_id          - ID of the framework adapter invoking the call
 *  @param callback_framework_id - ID of the framework waiting for the callback
 *  @param call_id               - ID of the process that was blocked
 *  @param time_unit             - Simulation time unit
 *  @param time_value            - Current simulatin time
 * 
 */
typedef void (*bp_notify_end_blocking_type)
(
     int              framework_id,
     int              callback_framework_id, 
     int              call_id,
     uvm_ml_time_unit time_unit,
     double           time_value
);


//******************************************************************************
// ----- Max Pack Size API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_get_pack_max_size() function ptr
/*! Get the maximum size of data packing from target framework
 *
 *  @param framework_id - unique id of the target framework
 *
 *  @return max size value returned from framework
 */
typedef int (*bp_get_pack_max_size_type)
(
    int framework_id
);

//------------------------------------------------------------------------------
//! typedef for bp_set_pack_max_size() function ptr
/*! Set the maximum size of data packing in target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param size         - max size value
 *
 *  @return void
 */
typedef void (*bp_set_pack_max_size_type)
(
    int framework_id,
    int size
);


//******************************************************************************
// ----- Type identification and mapping API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_get_type_id_from_name() function ptr
/*! Get the type id from target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param type_name    - the type name
 *
 *  @return - type id
 */
typedef uvm_ml_type_id_t (*bp_get_type_id_from_name_type)
(
    int         framework_id, 
    const char* type_name
); 

//------------------------------------------------------------------------------
//! typedef for bp_get_type_name_from_id() function ptr
/*! Get the type name from target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param type_id      - unique id of the type
 *
 *  @return - the type name
 */
typedef char* (*bp_get_type_name_from_id_type)
(
    int              framework_id,
    uvm_ml_type_id_t type_id
); 

//------------------------------------------------------------------------------
//! typedef for bp_set_match_types() function ptr
/*! Register matching types
 *
 *  @param type1 - Name of first type
 *  @param type2 - Name of second type
 *
 *  @return Return status
 *           - 1 : success
 *           - 0 : error type is not found or framework is not available
 */
typedef int (*bp_set_match_types_type)
(
    int         framework_id,
    const char* type1, 
    const char* type2
);


//******************************************************************************
// ----- TLM1 put API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_nb_put() function ptr
/*! Forward TLM1 non-blocking put transaction to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to target
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_nb_put_type)
(
    int              framework_id,
    int              producer_id,
    unsigned int     stream_size,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit,
    double           time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_can_put() function ptr
/*! Forward TLM1 can_put request to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_can_put_type)
(
    int              framework_id, 
    int              producer_id,
    uvm_ml_time_unit time_unit,
    double           time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_request_put() function ptr
/*! Forward TLM1 put request to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param call_id      - unique id of transaction
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to target
 *  @param done         - indicate end of fake blocking protocol
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_request_put_type)
(
    int                framework_id,
    int                producer_id,
    int                call_id, 
    unsigned int       stream_size, 
    uvm_ml_stream_t    stream,
    /*! Argument done is needed because a calling framework does not know whether 
        the called framework supports non-preemptive blocking or preemptive blocking protocol */
    unsigned int     * done,
    uvm_ml_time_unit * time_unit,
    double           * time_value
); 


//------------------------------------------------------------------------------
//! typedef for TLM1 bp_put() function ptr
/*! Forward TLM1 put transaction to target framework
 *
 *  @param framework_id     - unique id of the target framework
 *  @param port_connector_id
 *  @param stream_size      - size of data stream
 *  @param stream           - data stream sent to target
 *  @param time_unit        - time units
 *  @param time_value       - current time
 *
 *  @return 0
 */
typedef int (*bp_put_type)
(
    int                framework_id, 
    int                port_connector_id, 
    unsigned int       stream_size, 
    uvm_ml_stream_t    stream,
    uvm_ml_time_unit * time_unit,
    double           * time_value
);


//******************************************************************************
// ----- TLM1 get API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_nb_get() function ptr
/*! Forward TLM1 non-blocking get transaction to target framework
 *
 *  @param framework_id    - unique id of the target framework
 *  @param producer_id     - unique id of the initiating framework
 *  @param stream_size_ptr - size of data stream
 *  @param stream          - data stream pointer for result
 *  @param time_unit       - time units
 *  @param time_value      - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_nb_get_type)
(
    int               framework_id, 
    int               producer_id,
    unsigned int   *  stream_size_ptr,
    uvm_ml_stream_t   stream,
    uvm_ml_time_unit  time_unit,
    double            time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_can_get() function ptr
/*! Forward TLM1 can_get request to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_can_get_type)
( 
    int              framework_id, 
    int              producer_id,
    uvm_ml_time_unit time_unit,
    double           time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_request_get() function ptr
/*! Forward TLM1 get request to target framework
 *
 *  @param framework_id    - unique id of the target framework
 *  @param producer_id     - unique id of the initiating framework
 *  @param call_id         - unique id of transaction
 *  @param stream_size_ptr - size of data stream
 *  @param stream          - data stream pointer for result
 *  @param done            - indicate end of fake blocking protocol
 *  @param time_unit       - time units
 *  @param time_value      - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_request_get_type) 
(
    int             framework_id,
    int             producer_id,
    int             call_id,
    unsigned int *  stream_size_ptr,
    uvm_ml_stream_t stream,
    unsigned int *  done,
    uvm_ml_time_unit * time_unit,
    double           * time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_get_requested() function ptr
/*! Obtain TLM1 get result from target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param call_id      - unique id of transaction
 *  @param stream       - data stream returned to caller
 *
 *  @return response from target framework
 */
typedef unsigned int (*bp_get_requested_type) 
(
     int              framework_id,
     int              producer_id,
     int              call_id,
     uvm_ml_stream_t  stream
);

//------------------------------------------------------------------------------
//! typedef for bp_get() function ptr
/*! Forward TLM1 get transaction to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param stream       - data stream pointer for result
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return 0
 */
typedef int (*bp_get_type)
(
    int                framework_id,
    int                producer_id,
    uvm_ml_stream_t    stream,
    uvm_ml_time_unit * time_unit,
    double           * time_value
);


//******************************************************************************
// ----- TLM1 peek API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_nb_peek() function ptr
/*! Forward TLM1 non-blocking peek transaction to target framework
 *
 *  @param framework_id    - unique id of the target framework
 *  @param producer_id     - unique id of the initiating framework
 *  @param stream_size_ptr - size of data stream
 *  @param stream          - data stream pointer for result
 *  @param time_unit       - time units
 *  @param time_value      - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_nb_peek_type)
(
    int              framework_id,
    int              producer_id,
    unsigned int *   stream_size_ptr,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit,
    double           time_value
); 

//------------------------------------------------------------------------------
//! typedef for bp_can_peek() function ptr
/*! Forward TLM1 can_peek request to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_can_peek_type)
(
    int              framework_id,
    int              producer_id,  
    uvm_ml_time_unit time_unit,
    double           time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_request_peek() function ptr
/*! Forward TLM1 peek request to target framework
 *
 *  @param framework_id    - unique id of the target framework
 *  @param producer_id     - unique id of the initiating framework
 *  @param call_id         - unique id of transaction
 *  @param stream_size_ptr - size of data stream
 *  @param stream          - data stream pointer for result
 *  @param done            - indicate end of fake blocking protocol
 *  @param time_unit       - time units
 *  @param time_value      - current time
 *
 *  @return response from target framework
 */
typedef int (*bp_request_peek_type) 
(
    int                framework_id, 
    int                producer_id,
    int                call_id,
    unsigned int     * stream_size_ptr,
    uvm_ml_stream_t    stream,
    unsigned *         done,
    uvm_ml_time_unit * time_unit,
    double           * time_value
); 

//------------------------------------------------------------------------------
//! typedef for bp_peek_requested() function ptr
/*! Obtain TLM1 peek result target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param call_id      - unique id of transaction
 *  @param stream       - data stream returned to caller
 *
 *  @return response from target framework
 */
typedef unsigned int (*bp_peek_requested_type)
(
    int              framework_id,
    int              producer_id,
    int              call_id, 
    uvm_ml_stream_t  stream
);
  
//------------------------------------------------------------------------------
//! typedef for bp_peek() function ptr
/*! Forward TLM1 peek transaction to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of the initiating framework
 *  @param stream       - data stream pointer for result
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return 0
 */
typedef unsigned int (*bp_peek_type)
(
    int                framework_id,
    int                producer_id,
    uvm_ml_stream_t    stream,
    uvm_ml_time_unit * time_unit,
    double           * time_value
);


//******************************************************************************
// ----- TLM1 transport API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_nb_transport() function ptr
/*! Forward TLM1 non-blocking transport request to target framework
 *
 *  @param framework_id        - unique id of the target framework
 *  @param producer_id         - unique id of initiator
 *  @param req_stream_size     - size of the request stream
 *  @param req_stream          - request stream
 *  @param rsp_stream_size_ptr - size of the response stream
 *  @param rsp_stream          - response stream
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status returned from target framework
 */
typedef int (*bp_nb_transport_type)
(
    int               framework_id, 
    int               producer_id, 
    unsigned int      req_stream_size, 
    uvm_ml_stream_t   req_stream,
    unsigned int    * rsp_stream_size_ptr, 
    uvm_ml_stream_t   rsp_stream,
    uvm_ml_time_unit  time_unit,
    double            time_value
);

//------------------------------------------------------------------------------
//! typedef for bp_request_transport() function ptr
/*! Forward TLM1 transport request to target framework
 *
 *  @param framework_id    - unique id of the target framework
 *  @param producer_id     - unique id of initiator
 *  @param req_stream_size - size of the request stream
 *  @param req_stream      - request stream
 *  @param rsp_stream_size - size of the response stream
 *  @param rsp_stream      - response stream
 *  @param done            - indicate end of fake blocking protocol
 *  @param time_unit       - time units
 *  @param time_value      - current time
 *
 *  @return status returned from target framework
 */
typedef int (*bp_request_transport_type)
(
    int                framework_id, 
    int                producer_id,
    int                call_id,
    unsigned int       req_stream_size, 
    uvm_ml_stream_t    req_stream,
    unsigned int *     rsp_stream_size, 
    uvm_ml_stream_t    rsp_stream,
    /*! Argument done is needed because a calling framework does not know whether 
        the called framework supports blocking or fake blocking protocol */
    unsigned int *     done,
    uvm_ml_time_unit * time_unit,
    double           * time_value
); 

//------------------------------------------------------------------------------
//! typedef for bp_transport_response() function ptr
/*! Obtain TLM1 transport response to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of initiator
 *  @param call_id      - unique id of transaction
 *  @param rsp_stream   - response obtained from target
 *
 *  @return status returned from target framework
 */
typedef unsigned int (*bp_transport_response_type)
(
    int              framework_id, 
    int              producer_id,
    int              call_id,
    uvm_ml_stream_t  rsp_stream
); 

//------------------------------------------------------------------------------
//! typedef for bp_transport() function ptr
/*! Forward TLM1 transport transaction to target framework
 *
 *  @param framework_id    - unique id of the target framework
 *  @param producer_id     - unique id of initiator
 *  @param req_stream_size - size of the request stream
 *  @param req_stream      - request stream
 *  @param rsp_stream_size - size of the response stream
 *  @param rsp_stream      - response stream
 *  @param time_unit       - time units
 *  @param time_value      - current time
 *
 *  @return 0
 */
typedef int (*bp_transport_type)
(
    int                framework_id, 
    int                producer_id,
    unsigned int       req_stream_size, 
    uvm_ml_stream_t    req_stream,
    unsigned int     * rsp_stream_size, 
    uvm_ml_stream_t    rsp_stream,
    uvm_ml_time_unit * time_unit,
    double           * time_value
);


//******************************************************************************
// ----- Analysis API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_write() function ptr
/*! Forward analysis port message request to target frameworks
 *
 *  @param framework_id - unique id of the target framework
 *  @param producer_id  - unique id of initiator
 *  @param stream_size  - size of the message stream
 *  @param stream       - message stream
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status returned from target framework
 */
typedef void (*bp_write_type)
(
    int              framework_id, 
    int              producer_id, 
    unsigned int     stream_size, 
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit,
    double           time_value
);


//******************************************************************************
// ----- TLM2 API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for TLM2 bp_b_transport() function ptr
/*! Forward TLM2 blocking transport to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param initiator_id - unique id of the initiator framework
 *  @param stream_size  - size of the message stream
 *  @param stream       - message stream
 *  @param delay_unit   - time units for the delay attribute
 *  @param delay_value  - delay parameter attribute of the transaction
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return 0
 */
typedef int (*bp_b_transport_tlm2_type)
(
    int                framework_id, 
    int                initiator_id, 
    unsigned int     * stream_size,
    uvm_ml_stream_t  * stream,
    uvm_ml_time_unit * delay_unit,
    double           * delay_value,
    uvm_ml_time_unit   time_unit,
    double             time_value
);

//------------------------------------------------------------------------------
//! typedef for TLM2 bp_request_b_transport() function ptr
/*! Forward TLM2 blocking transport request to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param initiator_id - unique id of the initiator framework
 *  @param call_id      - unique id of the transaction
 *  @param stream_size  - size of the message stream
 *  @param stream       - message stream
 *  @param delay_unit   - time units for the delay attribute
 *  @param delay_value  - delay parameter attribute of the transaction
 *  @param done         - indicate end of fake blocking protocol
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status returned from target framework
 */
typedef int (*bp_request_b_transport_tlm2_type)
(
    int                framework_id, 
    int                initiator_id, 
    int                call_id,
    unsigned int *     stream_size,
    uvm_ml_stream_t  * stream,
    uvm_ml_time_unit   delay_unit,
    double             delay_value,
    unsigned int *     done, 
    uvm_ml_time_unit   time_unit, 
    double             time_value
);

//------------------------------------------------------------------------------
//! typedef for TLM2 bp_b_transport_response() function ptr
/*! Obtain TLM2 blocking transport response to target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param initiator_id - unique id of the initiator framework
 *  @param call_id      - unique id of the transaction
 *  @param stream_size  - size of the message stream
 *  @param stream       - message stream
 *
 *  @return status returned from target framework
 */
typedef int (*bp_b_transport_tlm2_response_type)
(
    int                framework_id, 
    int                initiator_id, 
    int                call_id,
    unsigned int *     stream_size,
    uvm_ml_stream_t    stream
);

//------------------------------------------------------------------------------
//! typedef for TLM2 bp_nb_transport_fw() function ptr
/*! Forward TLM2 non-blocking transport to target framework
 *
 *  @param framework_id   - unique id of the target framework
 *  @param initiator_id   - unique id of the initiator framework
 *  @param stream_size    - size of the message stream
 *  @param stream         - message stream
 *  @param phase          - phase attribute of the transaction
 *  @param transaction_id - unique id of the transaction
 *  @param delay_unit     - time units for the delay attribute
 *  @param delay_value    - delay parameter attribute of the transaction
 *  @param time_unit      - time units
 *  @param time_value     - current time
 *
 *  @return status returned from target framework
 */
typedef uvm_ml_tlm_sync_enum (*bp_nb_transport_fw_type)
(
    int                framework_id, 
    int                initiator_id,
    unsigned int *     stream_size,
    uvm_ml_stream_t *  stream,
    uvm_ml_tlm_phase * phase,
    unsigned int       transaction_id,
    uvm_ml_time_unit * delay_unit,
    double *           delay_value, 
    uvm_ml_time_unit   time_unit, 
    double             time_value
);
  
//------------------------------------------------------------------------------
//! typedef for TLM2 bp_nb_transport_bw() function ptr
/*! Backward TLM2 non-blocking transport
 *
 *  @param framework_id   - unique id of the target framework
 *  @param target_id      - unique id of the target framework
 *  @param stream_size    - size of the message stream
 *  @param stream         - message stream
 *  @param phase          - phase attribute of the transaction
 *  @param transaction_id - unique id of the transaction
 *  @param delay_unit     - time units for the delay attribute
 *  @param delay_value    - delay parameter attribute of the transaction
 *  @param time_unit      - time units
 *  @param time_value     - current time
 *
 *  @return status returned from target framework
 */
typedef uvm_ml_tlm_sync_enum (*bp_nb_transport_bw_type)
(
    int                framework_id, 
    int                target_id,
    unsigned int *     stream_size,
    uvm_ml_stream_t *  stream,
    uvm_ml_tlm_phase * phase,
    unsigned int       transaction_id,
    uvm_ml_time_unit * delay_unit,
    double *           delay_value, 
    uvm_ml_time_unit   time_unit, 
    double             time_value
);

//------------------------------------------------------------------------------
//! typedef for TLM2 bp_transport_dbg() function ptr
/*! 
 *  @param framework_id - unique id of the target framework
 *  @param socket_name  - name of the socket
 *
 *  @return void
 */
typedef unsigned int (*bp_transport_dbg_type)
(
    int               framework_id, 
    int               initiator_id,
    unsigned int *    stream_size,
    uvm_ml_stream_t * stream, 
    uvm_ml_time_unit  time_unit, 
    double            time_value
);


//------------------------------------------------------------------------------
//! typedef for bp_turn_off_transaction_mapping() function ptr
/*! 
 *  @param framework_id - unique id of the target framework
 *  @param socket_name  - name of the socket
 *
 *  @return void
 */
typedef void (*bp_turn_off_transaction_mapping_type)
(
    int          framework_id, 
    const char * socket_name
);

//------------------------------------------------------------------------------
//! typedef for bp_assign_transaction_id() function ptr
/*! Assign a unique id to a new transaction
 *
 *  @param framework_id - unique id of the target framework
 *
 *  @return - unique transaction id
 */
typedef unsigned int (*bp_assign_transaction_id_type)
(
    int framework_id
);


//******************************************************************************
// ----- Framework synchronization API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_synchronization() function ptr
/*! Advance time in target framework
 *
 *  @param framework_id - unique id of the target framework
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return void
 */
typedef void (*bp_synchronize_type)
(
    int              framework_id,
    uvm_ml_time_unit time_unit, 
    double           time_value
);


//******************************************************************************
// ----- ML Hierarchical Consruction API
//******************************************************************************

//------------------------------------------------------------------------------
//! typedef for bp_create_child_junction_node() function ptr
/*! Create a child junction node
 *
 *  @param framework_id               - Unique ID of the framework adapter
 *  @param target_framework_indicator - Target framework's indicator name 
 *  @param component_type_name        - Component type name of the child to be created
 *  @param instance_name              - Instance name of the child to be created
 *  @param parent_full_name           - Full hierarchical path name of the calling parent component
 *  @param parent_junction_node_id    - ID of the parent junction node
 *  
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
typedef int (*bp_create_child_junction_node_type)
(
    int            framework_id,
    const char   * target_framework_indicator,
    const char   * component_type_name,
    const char   * instance_name,
    const char   * parent_full_name,
    int            parent_junction_node_id
);

/*********************************************/
/* ML Configuration and Resources API */
/***********************************************/

typedef int (*bp_notify_resource_type)
(
    int                           framework_id,
    uvm_ml_resource_notify_action action,
    const char *                  item_scope,
    const char *                  item_name,
    const char *                  accessor_name,
    unsigned int                  stream_size,
    uvm_ml_stream_t               stream,
    uvm_ml_time_unit              time_unit, 
    double                        time_value
);

typedef void (*bp_notify_config_type)
(
    int              framework_id,
    const char *     cntxt,
    const char *     instance_name,
    const char *     field_name,
    unsigned int     stream_size,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit, 
    double           time_value
);



////////////////////////////////////////////////////////////////////////////////

/* =======================================
   Backplane Provided API function tray
   ===================================== */

//! Structure containing function pointers to the backplane provided API
typedef struct bp_api_struct {

// ----- Backplane and frameworks setup API

    BP_PROVIDED_API_FUNCTION(register_framework);       ///< bp_register_framework func ptr
    BP_PROVIDED_API_FUNCTION(get_version);              ///< bp_get_version func ptr
    BP_PROVIDED_API_FUNCTION(add_root_node);            ///< bp_add_root_node func ptr
    BP_PROVIDED_API_FUNCTION(run_test);                 ///< bp_run_test func ptr
    BP_PROVIDED_API_FUNCTION(reset);                    ///< bp_reset func ptr
    BP_PROVIDED_API_FUNCTION(set_trace_mode);           ///< bp_set_trace_mode func ptr

// ---- Service API

    BP_PROVIDED_API_FUNCTION(register_srv_providers);   ///< bp_register_srv_providers func ptr

// ---- Phasing API

    BP_PROVIDED_API_FUNCTION(notify_phase);             ///< bp_notify_phase func ptr
    BP_PROVIDED_API_FUNCTION(transmit_phase);           ///< bp_transmit_phase func ptr
    BP_PROVIDED_API_FUNCTION(notify_runtime_phase);     ///< bp_notify_runtime_phase func ptr
    BP_PROVIDED_API_FUNCTION(notify_phase_done);        ///< bp_notify_phase_done func ptr

// ----- TLM Common API

    BP_PROVIDED_API_FUNCTION(connect);                  ///< bp_connect func ptr
    BP_PROVIDED_API_FUNCTION(get_connector_size);       ///< bp_get_connector_size func ptr
    BP_PROVIDED_API_FUNCTION(notify_end_blocking);      ///< bp_notify_end_blocking func ptr

// ----- Max Pack Size API

    BP_PROVIDED_API_FUNCTION(get_pack_max_size);        ///< bp_get_pack_max_size func ptr
    BP_PROVIDED_API_FUNCTION(set_pack_max_size);        ///< bp_set_pack_max_size func ptr

// ----- Type identification and mapping API

    BP_PROVIDED_API_FUNCTION(get_type_id_from_name);    ///< bp_get_type_id_from_name func ptr
    BP_PROVIDED_API_FUNCTION(get_type_name_from_id);    ///< bp_get_type_name_from_id func ptr
    BP_PROVIDED_API_FUNCTION(set_match_types);          ///< bp_set_match_types func ptr

// ----- TLM1 put interface

    BP_PROVIDED_API_FUNCTION(nb_put);                   ///< bp_nb_put func ptr
    BP_PROVIDED_API_FUNCTION(can_put);                  ///< bp_can_put func ptr
    BP_PROVIDED_API_FUNCTION(request_put);              ///< bp_request_put func ptr
    BP_PROVIDED_API_FUNCTION(put);                      ///< bp_put func ptr

// ----- TLM1 get interface 

    BP_PROVIDED_API_FUNCTION(nb_get);                   ///< bp_nb_get func ptr
    BP_PROVIDED_API_FUNCTION(can_get);                  ///< bp_can_get func ptr
    BP_PROVIDED_API_FUNCTION(request_get);              ///< bp_request_get func ptr
    BP_PROVIDED_API_FUNCTION(get_requested);            ///< bp_get_requested func ptr
    BP_PROVIDED_API_FUNCTION(get);                      ///< bp_get func ptr
  
// ----- TLM1 peek interface

    BP_PROVIDED_API_FUNCTION(nb_peek);                  ///< bp_nb_peek func ptr
    BP_PROVIDED_API_FUNCTION(can_peek);                 ///< bp_can_peek func ptr
    BP_PROVIDED_API_FUNCTION(request_peek);             ///< bp_request_peek func ptr
    BP_PROVIDED_API_FUNCTION(peek_requested);           ///< bp_peek_requested func ptr
    BP_PROVIDED_API_FUNCTION(peek);                     ///< bp_peek func ptr

// ----- TLM1 transport interface

    BP_PROVIDED_API_FUNCTION(nb_transport);             ///< bp_nb_transport func ptr
    BP_PROVIDED_API_FUNCTION(request_transport);        ///< bp_request_transport func ptr
    BP_PROVIDED_API_FUNCTION(transport_response);       ///< bp_transport_response func ptr
    BP_PROVIDED_API_FUNCTION(transport);                ///< bp_transport func ptr

// ----- Analysis interface

    BP_PROVIDED_API_FUNCTION(write);                    ///< bp_write func ptr

// ----- TLM2 API

    BP_PROVIDED_API_FUNCTION(b_transport_tlm2);         ///< bp_b_transport_tlm2 func ptr
    BP_PROVIDED_API_FUNCTION(request_b_transport_tlm2); ///< bp_request_b_transport_tlm2 func ptr
    BP_PROVIDED_API_FUNCTION(b_transport_tlm2_response);///< bp_b_transport_tlm2_response func ptr
    BP_PROVIDED_API_FUNCTION(nb_transport_fw);          ///< bp_nb_transport_fw func ptr
    BP_PROVIDED_API_FUNCTION(nb_transport_bw);          ///< bp_nb_transport_bw func ptr
    BP_PROVIDED_API_FUNCTION(transport_dbg);            ///< bp_transport_dbg func ptr

    BP_PROVIDED_API_FUNCTION(turn_off_transaction_mapping); ///< bp_turn_off_transaction_mapping func ptr
    BP_PROVIDED_API_FUNCTION(assign_transaction_id);    ///< bp_assign_transaction_id func ptr

// ----- Framework synchronization API

    BP_PROVIDED_API_FUNCTION(synchronize);              ///< bp_synchronize func ptr

// ----- ML Hierarchical construction API

    BP_PROVIDED_API_FUNCTION(create_child_junction_node); ///< bp_create_child_junction_node func ptr

    /* Configuration and resources API */

  /*! Notify backplane of a resource item creation or update
    \param framework_id - unique id of the caller framework
    \param action - an enumeration indicating a resource setting operation
    \param item_scope - hierarchical scope for the notified resource
    \param item_name - name of the resource item
    \param accessor_name - full name of the context where the resource was set
    \stream_size - size of the message stream
    \stream - the message stream; may represent a packed typed object, an untyped raw stream (for integral values) or a stirng
    \time_unit - time units
    \time_value - current time
    \return void
   */
    BP_PROVIDED_API_FUNCTION(notify_resource);

  /*! Notify backplane of a configuration element creation or update
    \param framework_id - unique id of the caller framework
    \param cntxt - full hierarchical name of a quasi-static component where the configuration was set
    \param instance_name - instance name of the quasi-static component being configured
    \param field_name - name of the field being configured
    \stream_size - size of the message stream
    \stream - the message stream; may represent a packed typed object, an untyped raw stream (for integral values) or a stirng
    \time_unit - time units
    \time_value - current time
    \return void
   */
    BP_PROVIDED_API_FUNCTION(notify_config);
} bp_api_struct; 


extern bp_api_struct * bp_get_provided_tray();

///   @}   // end of BP_Provided group

#ifdef __cplusplus
}   // extern 'C'

#endif

#endif /* BP_PROVIDED_H */


