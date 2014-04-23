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

#ifndef UVM_ML_SV_H
#define UVM_ML_SV_H

extern "C" {

void uvm_ml_sv_set_trace_mode(int mode);

unsigned uvm_ml_sv_connect_ports(const char *   path1,
                                 const char *   path2);

int uvm_ml_sv_get_connector_size(int connector_id);

uvm_ml_type_id_t uvm_ml_sv_get_type_id_from_name(const char * type_name); 

const char* uvm_ml_sv_get_type_name_from_id(uvm_ml_type_id_t type_id); 

int uvm_ml_sv_try_put
(
    unsigned         export_connector_id, 
    unsigned         stream_size , 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_can_put
(
    unsigned         connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_try_get
(
    unsigned         export_connector_id, 
    unsigned *       stream_size_ptr, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_can_get
(
    unsigned connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_put_request
(
    unsigned         export_connector_id,
    unsigned         call_id, 
    unsigned         callback_adapter_id, 
    unsigned         stream_size, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_get
(
    unsigned           export_connector_id, 
    unsigned*          stream_size_ptr,
    uvm_ml_stream_t    stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
);

int uvm_ml_sv_get_request
(
    unsigned         export_connector_id, 
    unsigned         call_id,
    unsigned         callback_adapter_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

unsigned uvm_ml_sv_get_requested
(
    unsigned         export_connector_id, 
    unsigned         call_id,
    uvm_ml_stream_t  stream
);

int uvm_ml_sv_peek
(
    unsigned           export_connector_id, 
    unsigned*          stream_size_ptr,
    uvm_ml_stream_t    stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
);

int uvm_ml_sv_peek_request
(
    unsigned         export_connector_id, 
    unsigned         call_id,
    unsigned         callback_adapter_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

unsigned uvm_ml_sv_peek_requested
(
    unsigned         export_connector_id, 
    unsigned         call_id,
    uvm_ml_stream_t  stream
);

int uvm_ml_sv_try_peek
(
    unsigned         connector_id, 
    unsigned *       stream_size_ptr,
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_can_peek
(
    unsigned         connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_transport
(
    unsigned           export_connector_id, 
    unsigned           req_stream_size, 
    uvm_ml_stream_t    req_stream,
    unsigned*          rsp_stream_size, 
    uvm_ml_stream_t    rsp_stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
);

int uvm_ml_sv_transport_request
(
    unsigned         export_connector_id, 
    unsigned         call_id, 
    unsigned         callback_adapter_id, 
    unsigned         req_stream_size, 
    uvm_ml_stream_t  req_stream,
    unsigned*        rsp_stream_size, 
    uvm_ml_stream_t  rsp_stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

unsigned uvm_ml_sv_transport_response
(
    unsigned         producer_id, 
    unsigned         call_id,
    uvm_ml_stream_t  rsp_stream
);

int uvm_ml_sv_nb_transport
(
    unsigned         export_connector_id, 
    unsigned         req_stream_size, 
    uvm_ml_stream_t  req_stream,
    unsigned*        rsp_stream_size_ptr, 
    uvm_ml_stream_t  rsp_stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

void uvm_ml_sv_write
(
    unsigned         connector_id, 
    unsigned         stream_size, 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
);

int uvm_ml_sv_add_root_node
(
    unsigned         top_level_id,
    const char *     component_name,
    const char *     instance_name
);

void uvm_ml_sv_notify_runtime_phase
(
    char *              phase_group,
    char *              phase_name,
    uvm_ml_phase_action phase_action,
    unsigned int *      participate
);

int uvm_ml_sv_notify_phase_done
(
    char * phase_group,
    char * phase_name
);


void uvm_ml_sv_register_srv_providers
(
    bp_srv_provider_struct * provider
);

int uvm_ml_sv_tlm2_b_transport_request(unsigned         target_connector_id, 
                                       unsigned         call_id,
                                       unsigned         callback_adapter_id,
                                       unsigned         stream_size,
                                       uvm_ml_stream_t  stream,
                                       uvm_ml_time_unit delay_unit,
                                       double           delay_value, 
                                       uvm_ml_time_unit time_unit, 
                                       double           time_value);

int uvm_ml_sv_tlm2_b_transport_response(unsigned        initiator_id,
                                        unsigned        call_id,
                                        unsigned *      stream_size,
                                        uvm_ml_stream_t stream);

uvm_ml_tlm_sync_enum uvm_ml_sv_tlm2_nb_transport_incoming(unsigned           target_connector_id,
                                                          unsigned *         stream_size,
                                                          uvm_ml_stream_t *  stream,
                                                          uvm_ml_tlm_phase * phase,
                                                          unsigned int       transaction_id,
                                                          uvm_ml_time_unit * delay_unit,
                                                          double *           delay_value);

void uvm_ml_sv_turn_off_transaction_mapping(const char* socket_name);

unsigned int uvm_ml_sv_assign_transaction_id();

int uvm_ml_sv_set_match_types(const char* type1, const char* type2);

int uvm_ml_sv_synchronize();

int uvm_ml_sv_create_child_junction_node(const char *   target_framework_indicator,
                                         const char *   component_type_name,
                                         const char *   instance_name,
                                         const char *   parent_full_name,
                                         int            parent_junction_node_id);

void uvm_ml_sv_get_current_simulation_time(uvm_ml_time_unit * units, 
                                           double * value);

int uvm_ml_sv_notify_resource (uvm_ml_resource_notify_action action,
                               const char *                  item_scope,
                               const char *                  item_name,
                               const char *                  accessor_name,
                               unsigned int                  stream_size,
                               uvm_ml_stream_t               stream);

void uvm_ml_sv_notify_config (const char *    cntxt,
                              const char *    instance_name,
                              const char *    field_name,
                              unsigned int    stream_size,
                              uvm_ml_stream_t stream);
}   // extern 'C'

#endif
