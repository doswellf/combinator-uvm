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

// Required C API header file
// bp_required.h

#ifndef BP_REQUIRED_H
#define BP_REQUIRED_H

#include "bp_common_c.h"

/*! @mainpage Backplane required C API
 *
 *  @section API Backplane required C API
 *  This API defines the framework services required by the backplane.
 *
 *  @defgroup BP_Required Backplane required API.
 *  @{
 */

//! Macro for required API function ptr defines.
#define BP_REQUIRED_API_FUNCTION(f) frmw_##f##_type f##_ptr

#ifdef __cplusplus
extern "C" {
#endif

//******************************************************************************
// -----  Backplane and frameworks setup API
//******************************************************************************


//------------------------------------------------------------------------------
//! typdef for set_trace_mode function ptr
/*! Set tracing mode for the framework
*   @param mode - selected mode
*
*   @return void
*/
typedef void (* frmw_set_trace_mode_type)
(
    int mode
);

//------------------------------------------------------------------------------
//! typedef for startup function ptr
/*! Start the framework
 *
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
typedef int (* frmw_startup_type)();


//------------------------------------------------------------------------------
//! typedef for construct_top function ptr
/*!
 *  Create a top level root node.
 *  Called to the framework adapter to construct a root node of
 *  type top_identifier with instance named instance_name
 *
 *  @param top_identifier - type of the created root node
 *  @param instance_name  - instance name of the root node
 *
 *  @return unique id of the root node; -1 for error
 */
typedef int  (* frmw_construct_top_type)
(
    const char * top_identifier, 
    const char * instance_name
);

//------------------------------------------------------------------------------
//! typedef for get_top_component_for_arg function ptr
//
typedef char * (* frmw_get_top_component_for_arg_type) 
(
   char * arg
);

//******************************************************************************
// ----- Phasing API
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for transmit_phase function ptr
/*! Transmits phase notification to component specified by target_id.
 *  Called by backplane to all registered root nodes after phase master
 *  calls bp_notify_phase() or by a child proxy to a parent proxy.
 *
 *  @param target_id     - ID of the component to be phased
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
typedef int (*frmw_transmit_phase_type)
(
    int                 target_id,
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action
);

//------------------------------------------------------------------------------
//! typdef for notify_phase function ptr
/*! Notifies framework of non-time consuming phase.
 *
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
typedef int (*frmw_notify_phase_type)
(
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action
);

//------------------------------------------------------------------------------
//! typdef for notify_runtime_phase function ptr
/*! Notifies framework of time consuming phase.
 *
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param phase_action  - The action for this phase (start, execute,
 *                         ready to end, ended)
 *  @param time_unit     - Current simulation time unit
 *  @param time_value    - Current simulatin time scaled according to time_unit
 *  @param participate   - Output value to Indicate if the framework is 
 *                         participating in this phase
 * 
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
typedef int (*frmw_notify_runtime_phase_type)
(
    const char *        phase_group,
    const char *        phase_name,
    uvm_ml_phase_action phase_action,
    uvm_ml_time_unit    time_unit,
    double              time_value,
    unsigned int *      participate
);


//******************************************************************************
// ----- Phase Service API
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for phase_srv_start function ptr
/*! Called to phase service provider to start phasing.
 */
typedef void (*frmw_phase_srv_start_type) ();

//------------------------------------------------------------------------------
//! typdef for phase_srv_notify_phase_done function ptr
/*! Called to phase service provider to indicate framework is ready
 *  to exit phase.
 *
 *  @param framework_id  - Unique ID of the framework adapter that's notifying
 *                         phase done
 *  @param phase_group   - Name of the group the phase belongs in 
 *                         (eg. common, uvm ...)
 *  @param phase_name    - Name of the phase
 *  @param time_unit     - Current simulation time unit
 *  @param time_value    - Current simulatin time scaled according to time_unit
 */
typedef void (*frmw_phase_srv_notify_phase_done_type)
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
//! typdef for find_connector_id_by_name function ptr
/*! Return the unique id of the connector
 *
 *  @param path - the full path of the connector
 *
 *  @return the connector unique id
*/
typedef int (* frmw_find_connector_id_by_name_type)
(
    const char * path
);

//------------------------------------------------------------------------------
//! typdef for get_connector_intf_name function ptr
/*! Return the interface name of the connector
 *
 *  @param connector_id - unique id of the connector
 *
 *  @return the interface name of the connector
 */
typedef const char * (* frmw_get_connector_intf_name_type)
(
    unsigned connector_id
);

typedef const char * (* frmw_get_connector_T1_name_type)
(
    unsigned connector_id
);

typedef const char * (* frmw_get_connector_T2_name_type)
(
    unsigned connector_id
);

//------------------------------------------------------------------------------
//! typdef for is_export_connector function ptr
/*! Should be deprecated.
 *  Check if the connector is an export
 *
 *  @param connector_id - unique id of the connector
 *
 *  @return 0 for initiator socket or port; 1 otherwise
 */
typedef unsigned (* frmw_is_export_connector_type)
(
    unsigned connector_id
); /* DEPRECATE ME ! */

//------------------------------------------------------------------------------
//! typdef for get_connector_type function ptr
/*! Return the type of the connector
 *
 *  @param connector_id - unique id of the connector
 *
 *  @return the type name of the connector
 */
typedef int (* frmw_get_connector_type_type)
(
    unsigned connector_id
);

//------------------------------------------------------------------------------
//! typdef for external_connector function ptr
//
typedef void (* frmw_external_connect_type)
(
    unsigned connector_id
);

//------------------------------------------------------------------------------
//! typdef for notify_end_blocking function ptr
/*! Part of the pseudo-blocking mechanism. Notifies transaction has completed.
 *
 *  @param call_id    - unique id of transaction request
 *  @param time_unit  - Current simulation time unit
 *  @param time_value - Current simulatin time scaled according to time_unit
 */
typedef void (* frmw_notify_end_blocking_type) 
(
    unsigned         call_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);


//******************************************************************************
// ----- TLM1 put interface
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for try_put_uvm_ml_stream function ptr
/*! Implement TLM1 try_put transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_try_put_uvm_ml_stream_type)
(
    unsigned         connector_id, 
    unsigned         stream_size , 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for can_put function ptr
/*! Implement TLM1 can_put transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_can_put_type) 
(
    unsigned         connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for put_uvm_ml_stream function ptr
/*! Implement TLM1 put transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
  */
typedef int (* frmw_put_uvm_ml_stream_type) 
(
    unsigned           connector_id, 
    unsigned           stream_size, 
    uvm_ml_stream_t    stream, 
    uvm_ml_time_unit * time_unit, 
    double *           time_value
);

//------------------------------------------------------------------------------
//! typdef for put_uvm_ml_stream_request function ptr
/*! Implement TLM1 put request received from initiator framework
 *
 *  @param connector_id        - unique id of the connector
 *  @param call_id             - unique id of transaction
 *  @param callback_adapter_id - unique id of initiating adapter
 *  @param stream_size         - size of data stream
 *  @param stream              - data stream sent to initiator
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_put_uvm_ml_stream_request_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    unsigned         callback_adapter_id, 
    unsigned         stream_size, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//******************************************************************************
// ----- TLM1 get interface
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for get_uvm_ml_stream function ptr
/*! Implement TLM1 get transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_get_uvm_ml_stream_type) 
(
    unsigned           connector_id, 
    unsigned*          stream_size_ptr, 
    uvm_ml_stream_t    stream_ptr, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
);

//------------------------------------------------------------------------------
//! typdef for get_uvm_ml_stream_request function ptr
/*! Implement TLM1 get request received from initiator framework
 *
 *  @param connector_id        - unique id of the connector
 *  @param call_id             - unique id of transaction
 *  @param callback_adapter_id - unique id of initiating adapter
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_get_uvm_ml_stream_request_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    unsigned         callback_adapter_id, 
    uvm_ml_time_unit time_unit,
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for get_requested_uvm_ml_stream function ptr
/*! Send result of TLM1 get transaction to initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param call_id      - unique id of transaction
 *
 *  @return status of operation
 */
typedef unsigned (* frmw_get_requested_uvm_ml_stream_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    uvm_ml_stream_t  stream
);

//------------------------------------------------------------------------------
//! typdef for try_get_uvm_ml_stream function ptr
/*! Implement TLM1 try_get transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_try_get_uvm_ml_stream_type)
(
    unsigned         connector_id, 
    unsigned *       stream_size_ptr, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for can_get function ptr
/*! Implement TLM1 can_get transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_can_get_type) 
(
    unsigned         connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);


//******************************************************************************
// ----- TLM1 peek interface
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for peek_uvm_ml_stream function ptr
/*! Implement TLM1 peek transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_peek_uvm_ml_stream_type) 
(
    unsigned           connector_id, 
    unsigned *         stream_size_ptr, 
    uvm_ml_stream_t    stream_ptr, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
);

//------------------------------------------------------------------------------
//! typdef for peek_uvm_ml_stream_request function ptr
/*! Implement TLM1 peek request received from initiator framework
 *
 *  @param connector_id        - unique id of the connector
 *  @param call_id             - unique id of transaction
 *  @param callback_adapter_id - unique id of initiating adapter
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_peek_uvm_ml_stream_request_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    unsigned         callback_adapter_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for peek_requested_uvm_ml_stream function ptr
/*! Send result of TLM1 peek transaction to initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param call_id      - unique id of transaction
 *  @param stream       - data stream sent to initiator
 *
 *  @return status of operation
 */
typedef unsigned (* frmw_peek_requested_uvm_ml_stream_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    uvm_ml_stream_t  stream
);

//------------------------------------------------------------------------------
//! typdef for try_peek_uvm_ml_stream function ptr
/*! Implement TLM1 try_peek transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream sent to initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_try_peek_uvm_ml_stream_type)
(
    unsigned         connector_id, 
    unsigned *       stream_size_ptr, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for can_peek function ptr
/*! Implement TLM1 can_peek transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_can_peek_type) 
(
    unsigned         connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//******************************************************************************
// ----- TLM1 transport interface 
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for transport_uvm_ml_stream function ptr
/*! Implement TLM1 transport received from initiator framework
 *
 *  @param connector_id        - unique id of the connector
 *  @param req_stream_size     - size of request data stream
 *  @param req_stream          - request data stream
 *  @param rsp_stream_size_ptr - size of response data stream
 *  @param rsp_stream          - response data stream
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_transport_uvm_ml_stream_type) 
(
    unsigned           connector_id, 
    unsigned           req_stream_size, 
    uvm_ml_stream_t    req_stream,
    unsigned *         rsp_stream_size_ptr,
    uvm_ml_stream_t    rsp_stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
);

//------------------------------------------------------------------------------
//! typdef for transport_uvm_ml_stream_request function ptr
/*! Implement TLM1 transport request received from initiator framework
 *
 *  @param connector_id        - unique id of the connector
 *  @param call_id             - unique id of transaction request
 *  @param callback_adapter_id - unique id of the initiating adapter
 *  @param req_stream_size     - size of request data stream
 *  @param req_stream          - request data stream
 *  @param rsp_stream_size_ptr - size of response data stream
 *  @param rsp_stream          - response data stream
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_transport_uvm_ml_stream_request_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    unsigned         callback_adapter_id, 
    unsigned         req_stream_size, 
    uvm_ml_stream_t  req_stream,
    unsigned *       rsp_stream_size_ptr,
    uvm_ml_stream_t  rsp_stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for transport_response_uvm_ml_stream function ptr
/*! Send result of TLM1 transport transaction to initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param call_id      - unique id of transaction request
 *  @param rsp_stream   - response data stream
 *
 *  @return status of operation
 */
typedef unsigned (* frmw_transport_response_uvm_ml_stream_type) 
(
    unsigned         connector_id, 
    unsigned         call_id, 
    uvm_ml_stream_t  rsp_stream
);

//------------------------------------------------------------------------------
//! typdef for nb_transport_uvm_ml_stream function ptr
/*! Implement TLM1 non-blocking transport received from initiator framework
 *
 *  @param connector_id        - unique id of the connector
 *  @param req_stream_size     - size of request data stream
 *  @param req_stream          - request data stream
 *  @param rsp_stream_size_ptr - size of response data stream
 *  @param rsp_stream          - response data stream
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_nb_transport_uvm_ml_stream_type) 
(
    unsigned         connector_id, 
    unsigned         req_stream_size, 
    uvm_ml_stream_t  req_stream,
    unsigned*        rsp_stream_size_ptr,
    uvm_ml_stream_t  rsp_stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);


//******************************************************************************
// ----- Analysis interface
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for write_uvm_ml_stream function ptr
/*! Implement analysis transaction received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream received from initiator
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation
 */
typedef void (* frmw_write_uvm_ml_stream_type)
(
    unsigned         connector_id, 
    unsigned         stream_size, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);


//******************************************************************************
// ----- TLM2 interface
//******************************************************************************


//------------------------------------------------------------------------------
//! typdef for tlm2_b_transport function ptr
/*! Implement TLM2 blocking transport received from initiator framework
 *
 *  @param connector_id - unique id of the connector
 *  @param stream_size  - size of data stream
 *  @param stream       - data stream received from initiator
 *  @param delay_unit   - time units for delay attribute
 *  @param delay_value  - value of delay attribute of transaction
 *  @param time_unit    - time units
 *  @param time_value   - current time
 *
 *  @return status of operation; 0 for error
 */
typedef int (* frmw_tlm2_b_transport_type)
(
    unsigned           connector_id, 
    unsigned *         stream_size,
    uvm_ml_stream_t *  stream,
    uvm_ml_time_unit * delay_unit,
    double *           delay_value,
    uvm_ml_time_unit   time_unit, 
    double             time_value
);

//------------------------------------------------------------------------------
//! typdef for tlm2_b_transport_request function ptr
/*! Implement TLM2 blocking transport request received from initiator framework
 *
 *  @param target_connector_id - unique id of the connector
 *  @param call_id             - unique id of transaction request
 *  @param callback_adapter_id - unique id of the initiating adapter
 *  @param stream_size         - size of data stream
 *  @param stream              - data stream received from initiator
 *  @param delay_unit          - time units for delay attribute
 *  @param delay_value         - value of delay attribute of transaction
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef int (* frmw_tlm2_b_transport_request_type)
(
    unsigned         target_connector_id, 
    unsigned         call_id,
    unsigned         callback_adapter_id,
    unsigned         stream_size,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit delay_unit,
    double           delay_value, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

//------------------------------------------------------------------------------
//! typdef for tlm2_b_transport_response function ptr
/*! Send result of TLM2 transport transaction to initiator framework
 *
 *  @param target_connector_id - unique id of the connector
 *  @param call_id             - unique id of transaction request
 *  @param stream_size         - size of data stream
 *  @param stream              - data stream received from initiator
 *
 *  @return status of operation
 */
typedef int (* frmw_tlm2_b_transport_response_type)
(
    unsigned           target_connector_id, 
    unsigned           call_id,
    unsigned *         stream_size,
    uvm_ml_stream_t *  stream
);

//------------------------------------------------------------------------------
//! typdef for tlm2_nb_transport_fw function ptr
/*! Implement TLM2 non-blocking transport forward transaction received from initiator framework
 *
 *  @param target_connector_id - unique id of the connector
 *  @param stream_size         - size of data stream
 *  @param stream              - data stream received from initiator
 *  @param phase               - phase attribute of the transaction
 *  @param transaction_id      - unique id of transaction
 *  @param delay_unit          - time units for delay attribute
 *  @param delay_value         - value of delay attribute of transaction
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef uvm_ml_tlm_sync_enum (* frmw_tlm2_nb_transport_fw_type)
(
    unsigned            target_connector_id,
    unsigned *          stream_size,
    uvm_ml_stream_t *   stream,
    uvm_ml_tlm_phase *  phase,
    unsigned int        transaction_id,
    uvm_ml_time_unit *  delay_unit,
    double *            delay_value, 
    uvm_ml_time_unit    time_unit, 
    double              time_value
);

//------------------------------------------------------------------------------
//! typdef for tlm2_nb_transport_bw function ptr
/*! Implement TLM2 non-blocking transport backward transaction
 *
 *  @param target_connector_id - unique id of the connector
 *  @param stream_size         - size of data stream
 *  @param stream              - data stream received from initiator
 *  @param phase               - phase attribute of the transaction
 *  @param transaction_id      - unique id of transaction
 *  @param delay_unit          - time units for delay attribute
 *  @param delay_value         - value of delay attribute of transaction
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef uvm_ml_tlm_sync_enum (* frmw_tlm2_nb_transport_bw_type)
(
    unsigned            target_connector_id,
    unsigned *          stream_size,
    uvm_ml_stream_t *   stream,
    uvm_ml_tlm_phase *  phase,
    unsigned int        transaction_id,
    uvm_ml_time_unit *  delay_unit,
    double *            delay_value, 
    uvm_ml_time_unit    time_unit, 
    double              time_value
);

//------------------------------------------------------------------------------
//! typdef for tlm2_transport_dbg function ptr
/*! Implement TLM2 debug transport transaction received from initiator framework
 *
 *  @param target_connector_id - unique id of the connector
 *  @param stream_size         - size of data stream
 *  @param stream              - data stream received from initiator
 *  @param time_unit           - time units
 *  @param time_value          - current time
 *
 *  @return status of operation
 */
typedef unsigned int (* frmw_tlm2_transport_dbg_type)
(
    unsigned          target_connector_id,
    unsigned *        stream_size,
    uvm_ml_stream_t * stream, 
    uvm_ml_time_unit  time_unit, 
    double            time_value
);

//------------------------------------------------------------------------------
//! typdef for tlm2_turn_off_transaction_mapping function ptr
/*! Deactivate transaction mapping mode for TLM2 socket
 *
 *  @param socket_name - TLM2 socket name
 *
 *  @return void
 */
typedef void (* frmw_tlm2_turn_off_transaction_mapping_type)
(
    const char* socket_name
);



//******************************************************************************
// ----- Framework synchronization API
//******************************************************************************

//------------------------------------------------------------------------------
//! typdef for synchronization function ptr
/*! Advance time of framework
 *
 *  @param time_unit  - time units
 *  @param time_value - current time
 *
 *  @return void
 */
typedef void (* frmw_synchronize_type)
(
    uvm_ml_time_unit  time_unit, 
    double            time_value
);


//******************************************************************************
// -----  ML Hierarchical construction API
//******************************************************************************


//------------------------------------------------------------------------------
//! typdef for create_child_junction_node function ptr
/*! Creates child junction node
 * 
 *  @param component_type_name     - type name of the node to be created
 *  @param instance_name           - instance name of the node to be created
 *  @param parent_full_name        - full name of the parent of this child node
 *  @param parent_framework_id     - framework id of the parent
 *  @param parent_junction_node_id - id of the parent junction node
 *
 *  @return Return status
 *           - 1 : success
 *           - 0 : error
 */
typedef int (* frmw_create_child_junction_node_type)
(
    const char * component_type_name,
    const char * instance_name,
    const char * parent_full_name,
    int          parent_framework_id,
    int          parent_junction_node_id
);

typedef int (*frmw_notify_resource_type)
(
    uvm_ml_resource_notify_action action,
    const char *                  item_scope,
    const char *                  item_name,
    const char *                  accessor_name,
    unsigned int                  stream_size,
    uvm_ml_stream_t               stream,
    uvm_ml_time_unit              time_unit,
    double                        time_value
);

typedef void (*frmw_notify_config_type)
(
    const char *     cntxt,
    const char *     instance_name,
    const char *     field_name,
    unsigned int     stream_size,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit,
    double           time_value
);


//------------------------------------------------------------------------------
//! Required API (call-backs) function tray
/*! An instance of the tray is registered at the FrameworkProxyClass
 *  when the framework registers itself by calling
 *  BpInterconnect::RegisterFramework.
 *
 *  Tray elements are function pointers.
 */
typedef struct bp_frmw_c_api_struct {

    BP_REQUIRED_API_FUNCTION(set_trace_mode);               ///< set_trace_mode() function ptr
    BP_REQUIRED_API_FUNCTION(startup);                      ///< startup function ptr

    BP_REQUIRED_API_FUNCTION(construct_top);                ///< construct_top function ptr
    BP_REQUIRED_API_FUNCTION(get_top_component_for_arg);    ///< get_top_component_for_arg function ptr

// ----- Phasing API
    
    BP_REQUIRED_API_FUNCTION(transmit_phase);               ///< transmit_phase function ptr
    BP_REQUIRED_API_FUNCTION(notify_phase);                 ///< notify_phase function ptr
    BP_REQUIRED_API_FUNCTION(notify_runtime_phase);         ///< notify_runtime_phase function ptr

// ----- Phase Service API

    BP_REQUIRED_API_FUNCTION(phase_srv_start);              ///< phase_srv_start function ptr
    BP_REQUIRED_API_FUNCTION(phase_srv_notify_phase_done);  ///< phase_srv_notify_phase_done function ptr

// ----- TLM Common API

    BP_REQUIRED_API_FUNCTION(find_connector_id_by_name);    ///< find_connector_id_by_name function ptr
    BP_REQUIRED_API_FUNCTION(get_connector_intf_name);      ///< get_connector_intf_name function ptr
    BP_REQUIRED_API_FUNCTION(get_connector_type);           ///< get_connector_type function ptr
    BP_REQUIRED_API_FUNCTION(is_export_connector);          ///< is_export_connector function ptr
    BP_REQUIRED_API_FUNCTION(external_connect);             ///< external_connect function ptr
    BP_REQUIRED_API_FUNCTION(notify_end_blocking);          ///< notify_end_blocking function ptr

// ----- TLM1 put interface

    BP_REQUIRED_API_FUNCTION(try_put_uvm_ml_stream);        ///< try_put_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(can_put);                      ///< can_put function ptr
    BP_REQUIRED_API_FUNCTION(put_uvm_ml_stream);            ///< put_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(put_uvm_ml_stream_request);    ///< put_uvm_ml_stream_request function ptr

// ----- TLM1 get interface

    BP_REQUIRED_API_FUNCTION(get_uvm_ml_stream);            ///< get_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(get_uvm_ml_stream_request);    ///< get_uvm_ml_stream_request function ptr
    BP_REQUIRED_API_FUNCTION(get_requested_uvm_ml_stream);  ///< get_requested_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(try_get_uvm_ml_stream);        ///< try_get_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(can_get);                      ///< can_get function ptr

// ----- TLM1 peek interface

    BP_REQUIRED_API_FUNCTION(peek_uvm_ml_stream);           ///< peek_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(peek_uvm_ml_stream_request);   ///< peek_uvm_ml_stream_request function ptr
    BP_REQUIRED_API_FUNCTION(peek_requested_uvm_ml_stream); ///< peek_requested_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(try_peek_uvm_ml_stream);       ///< try_peek_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(can_peek);                     ///< can_peek function ptr

// ----- TLM1 transport interface 

    BP_REQUIRED_API_FUNCTION(transport_uvm_ml_stream);          ///< transport_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(transport_uvm_ml_stream_request);  ///< transport_uvm_ml_stream_request function ptr
    BP_REQUIRED_API_FUNCTION(transport_response_uvm_ml_stream); ///< transport_response_uvm_ml_stream function ptr
    BP_REQUIRED_API_FUNCTION(nb_transport_uvm_ml_stream);       ///< nb_transport_uvm_ml_stream function ptr

// ----- Analysis interface

    BP_REQUIRED_API_FUNCTION(write_uvm_ml_stream);          ///< write_uvm_ml_stream function ptr


// ----- TLM2 interface
 
    BP_REQUIRED_API_FUNCTION(tlm2_b_transport);             ///< tlm2_b_transport function ptr
    BP_REQUIRED_API_FUNCTION(tlm2_b_transport_request);     ///< tlm2_b_transport_request function ptr
    BP_REQUIRED_API_FUNCTION(tlm2_b_transport_response);    ///< tlm2_b_transport_response function ptr
    BP_REQUIRED_API_FUNCTION(tlm2_nb_transport_fw);         ///< tlm2_nb_transport_fw function ptr
    BP_REQUIRED_API_FUNCTION(tlm2_nb_transport_bw);         ///< tlm2_nb_transport_bw function ptr
    BP_REQUIRED_API_FUNCTION(tlm2_transport_dbg);           ///< tlm2_transport_dbg function ptr
    BP_REQUIRED_API_FUNCTION(tlm2_turn_off_transaction_mapping); ///< tlm2_turn_off_transaction_mapping function ptr

// ----- Framework synchronization API

    BP_REQUIRED_API_FUNCTION(synchronize);                  ///< synchronize function ptr

// -----  ML Hierarchical construction API

    BP_REQUIRED_API_FUNCTION(create_child_junction_node);   ///< create_child_junction_node function ptr


    BP_REQUIRED_API_FUNCTION(notify_resource);

    BP_REQUIRED_API_FUNCTION(notify_config);
} bp_frmw_c_api_struct;  // bp_frmw_c_api_struct

///   @}   // end of BP_Provided group

#ifdef __cplusplus
}   // extern 'C'
#endif

#endif /* BP_REQUIRED_H */
