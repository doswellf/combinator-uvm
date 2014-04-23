//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
//   Copyright 2013 Advanced Micro Devices Inc.
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

// /////////////////////////////////////////////
// File: uvm_ml_import_dpi.svh
//
// UVM_ML SV Adapter Import DPI Functions and Tasks
//
// Corresponds to Backplane Provided API
//
// /////////////////////////////////////////////

import "DPI-C" context uvm_ml_sv_set_trace_mode = function void uvm_ml_set_trace_mode(int mode);

import "DPI-C" context uvm_ml_sv_register_framework = function int uvm_ml_register_framework();

import "DPI-C" context uvm_ml_sv_add_root_node = function int uvm_ml_add_root_node(int unsigned top_level_id,
                                                                                   string       component_name,
                                                                                   string       instance_name);

import "DPI-C" context uvm_ml_sv_notify_phase = function int uvm_ml_notify_phase(string                phase_group,
                                                                                 string                phase_name,
                                                                                 uvm_ml_phase_action_e phase_action);

import "DPI-C" context uvm_ml_sv_transmit_phase = function int uvm_ml_transmit_phase(string                target_frmw_ind,
                                                                                     int                   target_id,
                                                                                     string                phase_group,
                                                                                     string                phase_name,
                                                                                     uvm_ml_phase_action_e phase_action);

import "DPI-C" context uvm_ml_sv_notify_runtime_phase = 
                       function uvm_ml_notify_runtime_phase(string                phase_group,
                                                            string                phase_name,
                                                            uvm_ml_phase_action_e phase_action,
                                                            output int unsigned   participate);

import "DPI-C" context uvm_ml_sv_connect_ports = function bit uvm_ml_connect(string       path1,
                                                                             string       path2);

import "DPI-C" context uvm_ml_sv_get_connector_size = function uvm_ml_get_connector_size(int unsigned local_port_id);

import "DPI-C" context uvm_ml_sv_nb_put = function bit uvm_ml_nb_put(int unsigned local_port_id, 
                                                                     int          packed_size, 
                                                                     `STREAM_T    stream);

import "DPI-C" context uvm_ml_sv_can_put = function bit uvm_ml_can_put(int unsigned local_port_id);

import "DPI-C" context uvm_ml_sv_nb_get = function bit uvm_ml_nb_get(int unsigned        local_port_id,
                                                                     output int unsigned stream_size,
                                                                     output `STREAM_T    stream);

import "DPI-C" context uvm_ml_sv_nb_peek = function bit uvm_ml_nb_peek(int unsigned        local_port_id,
                                                                       output int unsigned stream_size,
                                                                       output `STREAM_T    stream);

import "DPI-C" context uvm_ml_sv_can_get = function bit uvm_ml_can_get(int unsigned local_port_id);

import "DPI-C" context uvm_ml_sv_can_peek = function bit uvm_ml_can_peek(int unsigned local_port_id);

import "DPI-C" context uvm_ml_sv_nb_transport = function bit uvm_ml_nb_transport (int unsigned     local_port_id,
                                                                                  int              req_stream_size,
                                                                                  `STREAM_T        req_stream,
                                                                                  output int       rsp_stream_size,
                                                                                  output `STREAM_T rsp_stream);

import "DPI-C" context uvm_ml_sv_write = function void uvm_ml_write(int unsigned local_port_id, 
                                                                    int          packed_size, 
                                                                    `STREAM_T    stream);

import "DPI-C" context uvm_ml_sv_set_pack_max_size = function void uvm_ml_set_pack_max_size (int size);

import "DPI-C" context uvm_ml_sv_get_pack_max_size = function int uvm_ml_get_pack_max_size ();

import "DPI-C" context uvm_ml_sv_notify_end_blocking = 
                       function void uvm_ml_notify_end_task(int unsigned callback_adapter_id, 
                                                            int unsigned call_id);

import "DPI-C" context uvm_ml_sv_put_request = task uvm_ml_put_request(int unsigned        local_port_id,
                                                                       int unsigned        call_id,
                                                                       int unsigned        stream_size,
                                                                       `STREAM_T           stream,
                                                                       output int unsigned done);

import "DPI-C" context uvm_ml_sv_get_request = task uvm_ml_get_request(int unsigned        local_port_id,
                                                                       int unsigned        call_id,
                                                                       output int unsigned stream_size,
                                                                       output `STREAM_T    stream,
                                                                       output int unsigned done);

import "DPI-C" context uvm_ml_sv_get_requested = 
                       function int unsigned uvm_ml_get_requested(int unsigned     local_port_id,
                                                                  int unsigned     call_id,
                                                                  output `STREAM_T stream);

import "DPI-C" context uvm_ml_sv_peek_request = task uvm_ml_peek_request(int unsigned        local_port_id,
                                                                         int unsigned        call_id,
                                                                         output int unsigned stream_size,
                                                                         output `STREAM_T    stream,
                                                                         output int unsigned done);

import "DPI-C" context uvm_ml_sv_transport_request = 
                       task uvm_ml_transport_request(int unsigned        local_port_id,
                                                     int unsigned        call_id,
                                                     int unsigned        req_stream_size,
                                                     `STREAM_T           req_stream,
                                                     output int unsigned rsp_stream_size,
                                                     output `STREAM_T    rsp_stream,
                                                     output int unsigned done);

import "DPI-C" context uvm_ml_sv_transport_response = 
                       function int unsigned uvm_ml_transport_response(int unsigned     local_port_id,
                                                                       int unsigned     call_id,
                                                                       output `STREAM_T rsp_stream);

import "DPI-C" context uvm_ml_sv_set_match_types = 
                       function int uvm_ml_set_match_types(string type1, string type2);

import "DPI-C" context uvm_ml_sv_run_test = task uvm_ml_run_test(int unsigned adapter_id, 
                                                                 string       tops[], 
                                                                 string       test,
                                                                 output int   result);
      
import "DPI-C" context bp_in_ml_ovm_mode = function bit uvm_ml_in_ovm_mode(); // TODO: remove?

import "DPI-C" context bp_in_ml_uvm_mode = function bit uvm_ml_in_uvm_mode(); // TODO: remove?

import "DPI-C" context uvm_ml_sv_tlm2_nb_transport_fw = 
                       function uvm_tlm_sync_e uvm_ml_tlm2_nb_transport_fw(int unsigned             conn_id, 
                                                                           inout int unsigned       stream_size, 
                                                                           inout `STREAM_T          stream,
                                                                           inout uvm_tlm_phase_e    p, 
                                                                           input int unsigned       transaction_id, 
                                                                           inout uvm_ml_time_unit_e delay_unit, 
                                                                           inout real               delay_val);

import "DPI-C" context uvm_ml_sv_tlm2_nb_transport_bw = 
                       function uvm_tlm_sync_e uvm_ml_tlm2_nb_transport_bw(int unsigned             conn_id, 
                                                                           inout int unsigned       stream_size, 
                                                                           inout `STREAM_T          stream,
                                                                           inout uvm_tlm_phase_e    p, 
                                                                           input int unsigned       transaction_id, 
                                                                           inout uvm_ml_time_unit_e delay_unit, 
                                                                           inout real               delay_val);

import "DPI-C" context uvm_ml_sv_tlm2_b_transport_request = 
                       function int uvm_ml_tlm2_b_transport_request(int unsigned             conn_id,
                                                                    int unsigned             call_id,
                                                                    inout int unsigned       stream_size, 
                                                                    inout `STREAM_T          stream,
                                                                    input uvm_ml_time_unit_e delay_unit, 
                                                                    input real               delay_val,
                                                                    output int unsigned      done);

import "DPI-C" context uvm_ml_sv_tlm2_b_transport_response = 
                       function int uvm_ml_tlm2_b_transport_response(int unsigned        conn_id,
                                                                     int unsigned        call_id,
                                                                     output int unsigned stream_size, 
                                                                     output `STREAM_T    stream);

import "DPI-C" context uvm_ml_sv_turn_off_transaction_mapping = 
                       function void uvm_ml_turn_off_transaction_mapping(string socket_name);

import "DPI-C" context uvm_ml_sv_assign_transaction_id = 
                       function int unsigned uvm_ml_assign_transaction_id();


import "DPI-C" context uvm_ml_sv_get_type_id_from_name = 
                       function int uvm_ml_get_type_id_from_name(string typename);

import "DPI-C" context uvm_ml_sv_get_type_name_from_id = 
                       function string uvm_ml_get_type_name_from_id(int uni_type_id);

import "DPI-C" context uvm_ml_sv_synchronize = task uvm_ml_synchronize();


import "DPI-C" context uvm_ml_sv_create_child_junction_node = 
                       function int uvm_ml_create_child_junction_node(string     target_framework_indicator,
                                                                      string     component_type_name,
                                                                      string     instance_name,
                                                                      string     parent_full_name,
                                                                      int        parent_junction_node_id);

import "DPI-C" context uvm_ml_sv_notify_phase_done = task uvm_ml_notify_phase_done(string       phase_group, 
                                                                                   string       phase_name);

import "DPI-C" context uvm_ml_sv_register_srv_providers = function void uvm_ml_register_srv_providers(uvm_ml_srv_provider_struct srv_provider);

import "DPI-C" context uvm_ml_sv_notify_resource = function void uvm_ml_notify_resource(uvm_ml_resource_notify_action_e action,
                                                                                        string                          item_scope,
                                                                                        string                          item_name,
                                                                                        string                          accessor_name,
                                                                                        int unsigned                    stream_size,
                                                                                        `STREAM_T                       stream);

import "DPI-C" context uvm_ml_sv_notify_config = function void uvm_ml_notify_config(string       cntxt,
                                                                                    string       instance_name,
                                                                                    string       field_name,
                                                                                    int unsigned stream_size,
                                                                                    `STREAM_T    stream);

// /////////////////////////////////////////
//
// Package Scope User API functions 
// that call import "DPI" functions
//
// /////////////////////////////////////////

// /////////////////////////////////////////////////////////////////
//
// connect
//
function bit connect(string path1, string path2, bit map_transactions);

    bit    connection_result;

    if (trace_mode) begin
        string msg;
        $swrite(msg, "UVM-ML SV>> In connect for %s and %s", path1, path2);
        trace_msg(msg);
    end
      
    connection_result = uvm_ml_connect(path1,path2);
    if (map_transactions == 0) begin
        uvm_ml_turn_off_transaction_mapping(path1);
        uvm_ml_turn_off_transaction_mapping(path2);
    end
    return connection_result;
endfunction : connect

// /////////////////////////////////////////////////////////////////
//
// set_type_match
//
function int set_type_match(string type_name1, string type_name2);
    return uvm_ml_set_match_types (type_name1, type_name2);
endfunction : set_type_match
     
// /////////////////////////////////////////////////////////////////
//
// in_ml_ovm_mode
//
function bit in_ml_ovm_mode();
    in_ml_ovm_mode = uvm_ml_in_ovm_mode();
endfunction : in_ml_ovm_mode

// /////////////////////////////////////////////////////////////////
//
// in_ml_uvm_mode
//
function bit in_ml_uvm_mode();
    in_ml_uvm_mode = uvm_ml_in_uvm_mode();
endfunction : in_ml_uvm_mode

// /////////////////////////////////////////////////////////////////
//
// set_trace_mode
//
function void set_trace_mode(int mode);
    uvm_ml_set_trace_mode(mode);
endfunction : set_trace_mode
