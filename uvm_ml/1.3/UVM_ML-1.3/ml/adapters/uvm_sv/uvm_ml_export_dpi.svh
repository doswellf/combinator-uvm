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
// File: uvm_ml_export_dpi.svh
//
// UVM-ML SV Adapter export DPI functions and tasks. 
// Corresponds to Backplane Required API.
//
// /////////////////////////////////////////////

  export "DPI-C" uvm_ml_sv_export_set_trace_mode = function export_set_trace_mode;

  export "DPI-C" uvm_ml_sv_export_find_connector_id_by_name = function export_find_connector_id_by_name ;
  export "DPI-C" uvm_ml_sv_export_get_connector_intf_name = function export_get_connector_intf_name ;
  export "DPI-C" uvm_ml_sv_export_get_connector_T1_name = function export_get_connector_T1_name ;
  export "DPI-C" uvm_ml_sv_export_get_connector_T2_name = function export_get_connector_T2_name ;
  export "DPI-C" uvm_ml_sv_export_get_connector_type = function export_get_connector_type ;
  export "DPI-C" uvm_ml_sv_export_external_connect = function export_external_connect ;

  export "DPI-C" uvm_ml_sv_export_startup = function export_startup ;
  export "DPI-C" uvm_ml_sv_export_construct_top = function export_construct_top ;
  export "DPI-C" uvm_ml_sv_export_transmit_phase = function export_transmit_phase ;
  export "DPI-C" uvm_ml_sv_export_notify_phase = function export_notify_phase ;
  export "DPI-C" uvm_ml_sv_export_notify_runtime_phase = function export_notify_runtime_phase ;
  export "DPI-C" uvm_ml_sv_export_phase_srv_notify_phase_done = function export_phase_srv_notify_phase_done ;
  export "DPI-C" uvm_ml_sv_export_phase_srv_start = task export_phase_srv_start ;

  export "DPI-C" uvm_ml_sv_export_put_request = function export_put_request ;
  export "DPI-C" uvm_ml_sv_export_get_request = function export_get_request ;
  export "DPI-C" uvm_ml_sv_export_get_requested = function export_get_requested ;
  export "DPI-C" uvm_ml_sv_export_notify_end_blocking = function export_notify_end_blocking ;
  export "DPI-C" uvm_ml_sv_export_peek_request = function export_peek_request ;
  export "DPI-C" uvm_ml_sv_export_peek_requested = function export_peek_requested ;
  export "DPI-C" uvm_ml_sv_export_transport_request = function export_transport_request ;
  export "DPI-C" uvm_ml_sv_export_transport_response = function export_transport_response ;

  export "DPI-C" uvm_ml_sv_export_try_put = function export_try_put ;
  export "DPI-C" uvm_ml_sv_export_can_put = function export_can_put ;
  export "DPI-C" uvm_ml_sv_export_try_get = function export_try_get ;
  export "DPI-C" uvm_ml_sv_export_can_get = function export_can_get ;
  export "DPI-C" uvm_ml_sv_export_try_peek = function export_try_peek ;
  export "DPI-C" uvm_ml_sv_export_can_peek = function export_can_peek ;
  export "DPI-C" uvm_ml_sv_export_nb_transport = function export_nb_transport ;
  export "DPI-C" uvm_ml_sv_export_tlm_write = function export_write ;

  export "DPI-C" uvm_ml_sv_export_tlm2_nb_transport_incoming = function export_tlm2_nb_transport_incoming ;
  export "DPI-C" uvm_ml_sv_export_tlm2_b_transport_request = function export_tlm2_b_transport_request ;
  export "DPI-C" uvm_ml_sv_export_tlm2_b_transport_response = function export_tlm2_b_transport_response ;
  export "DPI-C" uvm_ml_sv_export_tlm2_turn_off_transaction_mapping = function export_tlm2_turn_off_transaction_mapping ;

  export "DPI-C" unilang_sv_blocking_calls_helper = function export_blocking_calls_helper;
  export "DPI-C" uvm_ml_sv_export_create_child_junction_node = function export_create_child_junction_node;

  export "DPI-C" uvm_ml_sv_export_notify_resource = function export_notify_resource;

  export "DPI-C" uvm_ml_sv_export_notify_config = function export_notify_config;

///////////////////////////////////


// /////////////////////////////////////////
//
// trace_export_call
//
// /////////////////////////////////////////

  function void trace_export_call(string call_name, string connection_name);
      string msg;
      $swrite(msg, "UVM-ML SV>> In %s. connector_id = %s", call_name, connection_name);
      trace_msg(msg);
  endfunction : trace_export_call

// /////////////////////////////////////////
//
// export_put_request
//
// /////////////////////////////////////////

  function void export_put_request(int unsigned connector_id, 
                                   int unsigned call_id, 
                                   int unsigned callback_adapter_id, 
                                   int unsigned stream_size, 
                                   `STREAM_T    stream);
      ml_tlm1_connector_base con;
      string                 msg;
      $cast(con,tlm_connector_base::get(connector_id));
      if (con == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: export put request failed because no connector was found for id %d", connector_id);
          `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_put_request", con.get_connection_name());

      active_b_put_connectors.push_back(con);
      put_stream_sizes.push_back(stream_size);
      put_stream_queue.push_back(stream);
      put_adapter_ids.push_back(callback_adapter_id);
      put_call_ids.push_back(call_id);
      put_call_defs.push_back(`UVM_ML_PUT_DEF);
  endfunction : export_put_request

// /////////////////////////////////////////
//
// pack_get
//
// /////////////////////////////////////////

  function void pack_get(`uvm_ovm_(object) obj, int unsigned call_id);

      get_stream_sizes[call_id] = 
          uvm_ml_serialization_kit::pack_cur_stream(obj, get_stream_queue[call_id]);
  endfunction : pack_get

// /////////////////////////////////////////
//
// push_back_get_stream_queue
//
// /////////////////////////////////////////

  function void push_back_get_stream_queue(input `STREAM_T stream, int unsigned call_id);
      get_stream_queue[call_id] = stream;
  endfunction : push_back_get_stream_queue

// /////////////////////////////////////////
//
// export_get_request
//
// /////////////////////////////////////////

  function void export_get_request(int unsigned connector_id, int unsigned call_id, int unsigned callback_adapter_id);
      ml_tlm1_connector_base con;
      string                 msg;
      `STREAM_T              stream;

      $cast(con,tlm_connector_base::get(connector_id));
      if (con == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: export get request failed because no connector was found for id %d", connector_id);
          `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_get_request", con.get_connection_name());

      active_b_get_connectors.push_back(con);
      get_adapter_ids.push_back(callback_adapter_id);
      get_call_ids.push_back(call_id);
      get_call_defs.push_back(`UVM_ML_GET_DEF);

      push_back_get_stream_queue(stream, call_id); // Use it to copy the vector
  endfunction : export_get_request

// /////////////////////////////////////////
//
// export_get_requested
//
// /////////////////////////////////////////

  function int unsigned export_get_requested(int unsigned     connector_id, 
		                             int unsigned     call_id, 
                                             output `STREAM_T stream);
    int unsigned size;
    string       msg;

    size = get_stream_sizes[call_id];
    if (trace_mode) begin
        tlm_connector_base con;
        $cast(con,tlm_connector_base::get(connector_id));
        if (con == null) begin
           $swrite(msg, 
                   "UVM-SV adapter: export get request failed because no connector was found for id %d", connector_id);
           `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
	end
        trace_export_call("export_get_requested", con.get_connection_name());
    end
    stream = get_stream_queue[call_id];
    return size;
  endfunction : export_get_requested

// /////////////////////////////////////////
//
// export_peek_request
//
// /////////////////////////////////////////

  function void export_peek_request(int unsigned connector_id, int unsigned call_id, int unsigned callback_adapter_id);
      ml_tlm1_connector_base con;
      string                 msg;
      `STREAM_T              stream;

      $cast(con,tlm_connector_base::get(connector_id));
      if (con == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: export peek request failed because no connector was found for id %d", connector_id);
          `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_peek_request", con.get_connection_name());

      active_b_get_connectors.push_back(con);
      get_adapter_ids.push_back(callback_adapter_id);
      get_call_ids.push_back(call_id);
      get_call_defs.push_back(`UVM_ML_PEEK_DEF);

      push_back_get_stream_queue(stream, call_id); // Use it to copy the vector
  endfunction : export_peek_request

// /////////////////////////////////////////
//
// export_peek_requested
//
// /////////////////////////////////////////

  function int unsigned export_peek_requested(int unsigned     connector_id, 
		                              int unsigned     call_id, 
                                              output `STREAM_T stream);
      return export_get_requested(connector_id,call_id,stream);
  endfunction : export_peek_requested

// /////////////////////////////////////////
//
// export_transport_request
//
// /////////////////////////////////////////

  function void export_transport_request(int unsigned        connector_id, 
                                         int unsigned        call_id,
                                         int unsigned        callback_adapter_id,
                                         int unsigned        req_stream_size,
                                         `STREAM_T           req_stream,
                                         output int unsigned stream_size,
                                         output `STREAM_T    stream);
      ml_tlm1_connector_base     con;
      string                     msg;
      $cast(con,tlm_connector_base::get(connector_id));
      if (con == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: export transport request failed because no connector was found for id %d", connector_id);
          `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_transport_request", con.get_connection_name());

      active_b_put_connectors.push_back(con);
      put_stream_sizes.push_back(req_stream_size);
      put_stream_queue.push_back(req_stream);
      put_adapter_ids.push_back(callback_adapter_id);
      put_call_ids.push_back(call_id);
      put_call_defs.push_back(`UVM_ML_TRANSPORT_DEF);
      active_b_get_connectors.push_back(con);
      get_adapter_ids.push_back(callback_adapter_id);
      get_call_ids.push_back(call_id);
      get_call_defs.push_back(`UVM_ML_TRANSPORT_DEF);
      push_back_get_stream_queue(stream, call_id); // Use it to copy the vector
  endfunction : export_transport_request

// /////////////////////////////////////////
//
// export_transport_response
//
// /////////////////////////////////////////

  function int unsigned export_transport_response(int unsigned     connector_id, 
		                                  int unsigned     call_id, 
                                                  output `STREAM_T stream);
      string msg;
      if (trace_mode) begin
          tlm_connector_base con;
          $cast(con,tlm_connector_base::get(connector_id));
	  if (con == null) begin
             $swrite(msg, 
                     "UVM-SV adapter: export transport response failed because no connector was found for id %d", connector_id);
             `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
	  end
          trace_export_call("export_transport_response", con.get_connection_name());
      end
      return export_get_requested(connector_id, call_id, stream);
  endfunction : export_transport_response

//====================================
//
// Package Body
//
//====================================

// /////////////////////////////////////////
//
// Function: initialize
//
// Initialize the framework. Register the adapter with the backplane 
// and register itself as the phase service and time service
// provider if corresponding bit is set, <sv_phase_master>, <sv_time_master>.
//
// Returns:
//
//  id - Adapter ID for this adapter
//
// /////////////////////////////////////////

  function int unsigned initialize();
      int id;
      uvm_ml_srv_provider_struct srv_providers;

      id = uvm_ml_register_framework();
      if(id < 0) begin
         `uvm_ovm_(report_error)("MLINITFW", "UVM-SV framework could not be registered");
      end;
      
      if (trace_mode) begin
          string       msg;
          $swrite(msg, "UVM-ML SV>> In initialize() with adapter_id = %d", id);
          trace_msg(msg);
      end

      if (sv_phase_master)
      begin
          srv_providers.phase_srv_provider = "UVM SV";
          uvm_ml_register_srv_providers(srv_providers);
      end

      uvm_resource_value_integral_notifier::type_id::set_type_override(uvm_ml_resource_value_integral_notifier::get_type());

      uvm_resource_value_object_notifier::type_id::set_type_override(uvm_ml_resource_value_object_notifier::get_type());

      uvm_resource_value_string_notifier::type_id::set_type_override(uvm_ml_resource_value_string_notifier::get_type());

      uvm_resource_options::turn_on_notifying();

      return id;
  endfunction : initialize

// /////////////////////////////////////////
//
// export_startup
//
// /////////////////////////////////////////

  function int export_startup();
      int unsigned         hier_id;
      int unsigned         top_id;
      `uvm_ovm_(component) top_comp;
      int                  res;
 
      uvm_ml_serialization_kit::initialize();
      uvm_ml_packer = new();

      if (`MAX_STREAM_BITSIZE != `UVM_OVM_(STREAMBITS))
          uvm_ml_set_pack_max_size(`MAX_STREAM_BITSIZE);

      for (top_id = 0; top_id < `uvm_ovm_(root)::get_num_top_levels(); top_id++) begin
          top_comp = `uvm_ovm_(root)::get_top_level_by_id(top_id);
          if (trace_mode) begin
              string msg;
              $swrite(msg,"UVM-ML SV>> In export_startup(). registering top = %s", top_comp.get_full_name());
              trace_msg(msg);
          end
          // Don't add phase master to backplane toplevel component list
          if (top_comp.get_name() != "uvm_ml_phase_service_inst")
          begin
              hier_id = get_hierarchical_node_id(top_comp);
              res = uvm_ml_add_root_node(hier_id, top_comp.get_name(), top_comp.get_full_name());
              if (res == (-1)) begin
                  `uvm_ovm_(report_error)("MLDUPTOP", "Duplicate top component instance name");
                  return 0;
              end
          end
      end
      return 1;
  endfunction : export_startup

// /////////////////////////////////////////
//
// export_construct_top
//
// /////////////////////////////////////////

  function int export_construct_top(string top_name, string instance_name);
      uvm_component result;
      int top_id;

      if (trace_mode) begin
          string msg;
          $swrite(msg,"UVM-ML SV>> In export_construct_top. Top_name = %s instance_name = %s", top_name, instance_name);
          trace_msg(msg);
      end
      result = `uvm_ovm_(root)::add_top_level(top_name, instance_name);
      if (result == null) begin
          `uvm_ovm_(report_fatal)("MLADDTOP", { "UVM-SV adapter: Can not create root node component of type ", top_name });
	  return -1;
      end;
      top_id = get_hierarchical_node_id(result);
      return top_id;
  endfunction : export_construct_top


// /////////////////////////////////////////
//
// export_notify_resource
//
// /////////////////////////////////////////

  function bit export_notify_resource(uvm_ml_resource_notify_action_e action,
                                      string                          scope,
                                      string                          name,
                                      string                          accessor_name,
                                      int unsigned                    stream_size,
                                      `STREAM_T                       stream);
      if (trace_mode) begin
          string msg;
          $swrite(msg, "UVM-ML SV>> In export_notify_resource. action = %d scope = %s name = %s accessor_name = %s stream_size = %d", action, scope, name, accessor_name, stream_size);
          trace_msg(msg);
      end
      return uvm_ml_set_resource(action, scope, name, accessor_name, stream_size, stream);
  endfunction : export_notify_resource

// /////////////////////////////////////////
//
// export_notify_config
//
// /////////////////////////////////////////

  function void export_notify_config(string       cntxt,
                                     string       instance_name,
                                     string       field_name,
                                     int unsigned stream_size,
                                     `STREAM_T    stream);
      string scope;

      if (trace_mode) begin
          string msg;
          $swrite(msg, "UVM-ML SV>> In export_notify_config. cntxt = %s instance_name = %s field_name = %s stream_size = %d", cntxt, instance_name, field_name, stream_size);
          trace_msg(msg);
      end
      if (instance_name == "")
          scope = cntxt;
      else if (cntxt == "")
          scope = instance_name;
      else
          scope = {cntxt, ".", instance_name};

      void'(uvm_ml_set_resource(UVM_ML_CONFIG_SET, scope, field_name, cntxt, stream_size, stream));
  endfunction : export_notify_config

//=============
// P H A S E S
//=============

// /////////////////////////////////////////
//
// Function: export_transmit_phase
//
// For non-runtime phase notification.
//
// Called by the backplane to notify a top level component of a phase
// or by hierachical parent to notify child of a phase.
//
// When the master phase controller calls bp_notify_phase(), the 
// backplane will notify each registered framework of the phase via
// notify_phase() and then notify each registered top of the phase
// via transmit_phase().
// 
// Some frameworks have phases that applied to the entire framework and 
// are not hierarchical, therefore the backplane splits the notify_phase()
// called by the master phase controller into two calls.  One to the 
// framework (notify_phase), so it can executed any framework specific
// phasing and then to the top components (transmit_phase) to do 
// hierachical phasing.
//
// In a unified hierarchy, a child proxy is created for a component that
// is in another framework. This child proxy is connected through the
// backplane to a parent proxy.  All non-time consuming phase notification
// the child proxy receieves is passed to the parent proxy through
// the bp_transmit_phase() called.  Runtime (time consuming) phases are
// non-hierarchical, and are phased by the framework when it recevies
// notification.
// 
// Parameters:
//
//  target_id    - ID of the hierarchical_node to phase from
//  phase_group  - Name of the group/domain the phase belongs to
//  phase_name   - Name of the phase
//  phase_action - Action for this phase (STARTED, EXECTUING, 
//                 ENDED)
//
// Returns:
//
//  Status : 
//      - 0 : failed
//      - 1 : success
//
// /////////////////////////////////////////

  function int  export_transmit_phase(int unsigned          target_id, 
                                      string                phase_group, 
                                      string                phase_name,
                                      uvm_ml_phase_action_e phase_action);
      uvm_domain      domain;
      uvm_phase       phase;
      uvm_component   comp;
      uvm_phase_state state;

      if (trace_mode) begin
          string msg;
          $swrite(msg,"UVM-ML SV>> In export_transmit_phase. phase_name = %s phase_action %0d target_id = %0d", phase_name, phase_action, target_id);
          trace_msg(msg);
      end

      if(target_id >= hierarchical_nodes.size) begin
         string msg;
	 $swrite(msg, 
		 "UVM-SV adapter: received illegal junction node ID %d", target_id);
	 `uvm_ovm_(report_error) ("MLNODEID", msg);
	 return 0;
      end;	      

      // If this SV is the phase master
      if (uvm_ml_phase_service_mgr)
      begin
          // master phaser takes cares of resovle_bindings
          // which is per framework
          if (phase_name != "resolve_bindings")
          begin
              if (phase_group == "common")
                  domain = uvm_domain::get_common_domain();
              else
                  domain = uvm_domain::get_uvm_domain();

              phase = domain.find_by_name(phase_name);
              comp  = hierarchical_nodes[target_id];
              phase.m_imp.traverse(comp, phase, phase.get_state());

              return 1;
          end
      end
      else begin
          state = get_phase_state(phase_action);
          return uvm_ml_phase::ml_do_nonblocking_phase(hierarchical_nodes[target_id], phase_name, state);
      end

  endfunction : export_transmit_phase

// /////////////////////////////////////////
//
// Function: export_notify_phase
//
// Called by the backplane to notify the framework of a
// non-runtime phase.
//
// When the master phase controller calls bp_notify_phase(), the 
// backplane will notify each registered framework of the phase via
// notify_phase() and then notify each registered top of the phase
// via transmit_phase().
// 
// Parameters:
//
//  phase_group  - Name of the group/domain the phase belongs to
//  phase_name   - Name of the phase
//  phase_action - Action for this phase (STARTED, EXECTUING, 
//                 ENDED)
//
// Returns:
//
//  Status : 
//      - 0 : failed
//      - 1 : success
//
// /////////////////////////////////////////

  function int  export_notify_phase(string                phase_group, 
                                    string                phase_name,
                                    uvm_ml_phase_action_e phase_action);

    `uvm_ovm_(root) root_object;
    uvm_phase       phase;
    root_object = `uvm_ovm_(root)::get();

    if (phase_name == "build") begin
        if (phase_action == UVM_ML_PHASE_STARTED)
            root_object.m_current_phase = root_object.get_phase_by_name(phase_name);
        else if (phase_action == UVM_ML_PHASE_EXECUTING) begin
            root_object.m_phasing_active++;
            phase = root_object.get_phase_by_name(phase_name);
            root_object.build_phase(phase); // executes build - specific settings
            root_object.m_phasing_active--;
        end
    end
    // When SV is the master phaser, it will take care of resolve_bindings
    if (uvm_ml_phase_service_mgr == null)
    begin
        if ((phase_name == "resolve_bindings")  &&
            (phase_action == UVM_ML_PHASE_EXECUTING) )
        begin
            root_object.do_resolve_bindings();
        end
    end

    export_notify_phase = 1;
  endfunction : export_notify_phase

// /////////////////////////////////////////
//
// Function: export_notify_runtime_phase
//
// Called by the backplane to notify the framework of a runtime 
// (time consuming) phase.
//
// No need to do anything if SV is the master phase controller.
// uvm_phase scheduler will fork off all run_phase task.
// 
// When SV is the phase slave:
//
// For runtime phases, the framework could choose to particpate
// in the phase or not by setting the participate bit to 1.
// If the framework participates in the phase, it means the
// phase controller will wait until the framework notifies it
// that it is ready to exit the phase (via bp_notify_phase_done)
// before continuing to the next phase.
//
// For SV, it will always set participate to be 1, and 
// fork off a particpate_handler to monitor phase_done objection
// can call notify_phase_done when appropriate.
//
// Parameters:
//
//  phase_group  - Name of the group/domain the phase belongs to
//  phase_name   - Name of the phase
//  phase_action - Action for this phase (STARTED, EXECTUING, 
//                 ENDED)
//  participate  - Output variable indicating whether this 
//                 framework is going to participate in this phase.
//
// /////////////////////////////////////////

  function void export_notify_runtime_phase(string                phase_group, 
                                            string                phase_name, 
                                            uvm_ml_phase_action_e phase_action,
                                            output int unsigned   participate);

    uvm_ml_phase_participate_handler participate_handler;

    uvm_phase_state state;                                                
    `uvm_ovm_(root) root_object;
    bit             result;

    root_object = `uvm_ovm_(root)::get();
    participate = 0;

    if (trace_mode) begin
        string msg;
        $swrite(msg,"UVM-ML SV>> In export_notify_runtime_phase. phase_name = %s phase_action = %d", 
                phase_name, phase_action);
        trace_msg(msg);
    end

    // If this SV is the phase master, SV top component will 
    // be phased automatically, don't need to execute phase
    if (uvm_ml_phase_service_mgr)
        return;

    state = get_phase_state(phase_action);

    if (phase_action == UVM_ML_PHASE_EXECUTING)
    begin
        uvm_ml_phase::ml_do_blocking_phase(root_object, phase_name, state);

        // Always participate in the phase and allow handler to call
        // notify_phase_done() to master phaser when all objections
        // are dropped or if there are no objections
        participate_handler = new(phase_name, phase_group);
        participate = 1;
        participate_handler.execute();
    end
    else
    begin
        void'(uvm_ml_phase::ml_do_nonblocking_phase(root_object, phase_name, state));
    end

  endfunction : export_notify_runtime_phase

// /////////////////////////////////////////
//
// export_set_trace_mode
//
// /////////////////////////////////////////

  function void export_set_trace_mode(int mode);
      trace_mode = mode;
  endfunction : export_set_trace_mode

// /////////////////////////////////////////
//
// export_find_connector_id_by_name
//
// /////////////////////////////////////////

  function int export_find_connector_id_by_name(string name);
      int                    connector_id;
      string                 msg;

      connector_id = ml_tlm2_imp::find_tlm2_connector_by_inst_name(name);
      if (connector_id == -1)
          connector_id = tlm_connector_base::find_connector_by_inst_name(name);

      if (trace_mode) begin
          tlm_connector_base con;
   
	  $cast(con,tlm_connector_base::get(connector_id));
	  if (con == null) begin
             $swrite(msg, 
                     "UVM-SV adapter: no connector was found for id %d", connector_id);
             `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
	     return -1;
	  end
          trace_export_call("export_find_connector_id_by_name", con.get_connection_name());
      end
      return connector_id;    
  endfunction : export_find_connector_id_by_name

// /////////////////////////////////////////
//
// export_get_connector_intf_name
//
// /////////////////////////////////////////

  function string export_get_connector_intf_name(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;

      con = tlm_connector_base::get(connector_id);

      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: no connector was found for id %d", connector_id);
         `uvm_ovm_(report_error) ("MLTLM2CONID", msg);
	 return "";
      end
      if (trace_mode)
          trace_export_call("export_get_connector_intf_name", con.get_connection_name());
      return con.get_if_name();
  endfunction : export_get_connector_intf_name

// /////////////////////////////////////////
//
// export_get_connector_T1_name
//
// /////////////////////////////////////////

  function string export_get_connector_T1_name(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;

      con = tlm_connector_base::get(connector_id);

      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: no connector was found for id %d", connector_id);
         `uvm_ovm_(report_error) ("MLTLM2CONID", msg);
	 return "";
      end
      if (trace_mode)
          trace_export_call("export_get_connector_T1_name", con.get_connection_name());
      return con.get_T1_name();
  endfunction : export_get_connector_T1_name

// /////////////////////////////////////////
//
// export_get_connector_T2_name
//
// /////////////////////////////////////////

  function string export_get_connector_T2_name(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;

      con = tlm_connector_base::get(connector_id);

      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: no connector was found for id %d", connector_id);
         `uvm_ovm_(report_error) ("MLTLM2CONID", msg);
	 return "";
      end
      if (trace_mode)
          trace_export_call("export_get_connector_T2_name", con.get_connection_name());
      return con.get_T2_name();
  endfunction : export_get_connector_T2_name

// /////////////////////////////////////////
//
// export_get_connector_type
//
// /////////////////////////////////////////

  function int export_get_connector_type(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);

      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: no connector was found for id %d", connector_id);
         `uvm_ovm_(report_error) ("MLTLM2CONID", msg);
	 return -1;
      end
      if (trace_mode)
          trace_export_call("export_get_connector_type", con.get_connection_name());
      return con.get_type();
  endfunction : export_get_connector_type

// /////////////////////////////////////////
//
// export_try_put
//
// /////////////////////////////////////////

  function bit export_try_put(int unsigned connector_id, 
                              int unsigned stream_size,
                              `STREAM_T    stream);

      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);

      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end
      if (trace_mode)
          trace_export_call("export_try_put", con.get_connection_name());

      if(stream_size <= 0) begin
         $swrite(msg, 
                 "UVM-SV adapter: adapter got empty stream for connector id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2EMPTY", msg);
      end

      return con.export_try_put(stream_size, stream);
  endfunction : export_try_put

// /////////////////////////////////////////
//
// export_can_put
//
// /////////////////////////////////////////

  function bit export_can_put(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: can_put failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_can_put", con.get_connection_name());
      return con.export_can_put();
  endfunction : export_can_put

// /////////////////////////////////////////
//
// export_try_get
//
// /////////////////////////////////////////

  function bit export_try_get(int unsigned        connector_id, 
                              output int unsigned stream_size,
                              output `STREAM_T    stream);

      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: try_get failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_try_get", con.get_connection_name());
      return con.export_try_get(stream_size, stream);
  endfunction : export_try_get

// /////////////////////////////////////////
//
// export_can_get
//
// /////////////////////////////////////////

  function bit export_can_get(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: can_get failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_can_get", con.get_connection_name());
      return con.export_can_get();
  endfunction : export_can_get

// /////////////////////////////////////////
//
// export_try_peek
//
// /////////////////////////////////////////

  function bit export_try_peek(int unsigned        connector_id, 
                               output int unsigned stream_size,
                               output `STREAM_T    stream);
      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: try_peek failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_try_peek", con.get_connection_name());
      return con.export_try_peek(stream_size, stream);
  endfunction : export_try_peek

// /////////////////////////////////////////
//
// export_can_peek
//
// /////////////////////////////////////////

  function bit export_can_peek(int unsigned connector_id);
      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: can_peek failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_can_peek", con.get_connection_name());
      return con.export_can_peek();
  endfunction : export_can_peek

// /////////////////////////////////////////
//
// export_nb_transport
//
// /////////////////////////////////////////

  function bit export_nb_transport(int unsigned        connector_id, 
                                   int unsigned        req_stream_size,
                                   `STREAM_T           req_stream,
                                   output int unsigned rsp_stream_size,
                                   output `STREAM_T    rsp_stream);
      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: nb_transport failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_nb_transport", con.get_connection_name());
      return con.export_nb_transport(req_stream_size, req_stream, rsp_stream_size, rsp_stream);
  endfunction : export_nb_transport

// /////////////////////////////////////////
//
// export_write
//
// /////////////////////////////////////////
  
  function void export_write(int unsigned connector_id, 
                             int unsigned stream_size,
                             `STREAM_T    stream);
    tlm_connector_base con;
    string             msg;
    con = tlm_connector_base::get(connector_id);
    if (con == null) begin
       $swrite(msg, 
               "UVM-SV adapter: write failed because no connector was found for id %d", connector_id);
       `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
    end

    if (trace_mode)
        trace_export_call("export_write", con.get_connection_name());

    if(stream_size <= 0) begin
       $swrite(msg, 
               "UVM-SV adapter: write failed because UVM-SV adapter got empty stream for connector id %d", connector_id);
       `uvm_ovm_(report_fatal) ("MLTLM2EMPTY", msg);
    end;

    con.export_write(stream_size, stream);
  endfunction : export_write

// /////////////////////////////////////////
//
// export_external_connect
//
// /////////////////////////////////////////
  

  function void export_external_connect(int unsigned connector_id);

      tlm_connector_base con;
      string             msg;
      con = tlm_connector_base::get(connector_id);
      if (con == null) begin
         $swrite(msg, 
                 "UVM-SV adapter: get failed because no connector was found for id %d", connector_id);
         `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end

      if (trace_mode)
          trace_export_call("export_external_connect", con.get_connection_name());
      con.do_connect();
  endfunction : export_external_connect

// /////////////////////////////////////////
//
// export_phase_srv_start
//
// /////////////////////////////////////////

  task export_phase_srv_start();
      uvm_ml_phase_service_mgr = uvm_ml_phase_service::get_inst();
      uvm_ml_phase_service_mgr.start_phasing();
  endtask : export_phase_srv_start
  

// /////////////////////////////////////////
//
// export_phase_srv_notify_phase_done
//
// /////////////////////////////////////////

  function void export_phase_srv_notify_phase_done(int unsigned       framework_id,
                                          string             phase_group,
                                          string             phase_name,
                                          uvm_ml_time_unit_e time_unit,
                                          real               time_value);
      uvm_ml_phase_service_mgr.srv_notify_phase_done(phase_group, phase_name);      
  endfunction : export_phase_srv_notify_phase_done




// /////////////////////////////////////////
//
// export_create_child_junction_node
//
// /////////////////////////////////////////
    
  function int export_create_child_junction_node(string component_type_name,
						 string instance_name,
						 string parent_full_name,
						 int    parent_framework_id,
						 int    parent_junction_node_id
						 ); 
      
      return parent_proxy::create_parent_proxy(component_type_name, instance_name, parent_full_name, parent_framework_id, parent_junction_node_id);
      
  endfunction : export_create_child_junction_node
