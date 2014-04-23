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

//------------------------------------
//
// =====================
// Blocking calls helper mechanism
//
//------------------------------------

  class blocking_call_id_class;
      int unsigned call_id;
      event        done;
      task wait_end_blocking();
	  @(done);
      endtask : wait_end_blocking
  endclass : blocking_call_id_class

  ml_tlm1_connector_base active_b_put_connectors[$];
  ml_tlm1_connector_base active_b_get_connectors[$];

  int unsigned           put_stream_sizes[$];
  `STREAM_T              put_stream_queue[$];
  int unsigned           get_stream_sizes[int unsigned];
  `STREAM_T              get_stream_queue[int unsigned];
  // Unfortunately the above does not work because multiple dimensions for queue or associative array is not implemented yet
  
  int unsigned           put_adapter_ids[$];
  int unsigned           put_call_ids[$];
  int unsigned           put_call_defs[$];
  int unsigned           get_adapter_ids[$];
  int unsigned           get_call_ids[$];
  int unsigned           get_call_defs[$];

  blocking_call_id_class blocking_call_ids[$];
  int unsigned           last_blocking_call_id = 0;

// /////////////////////////////////////////
//
// export_blocking_calls_helper
//
// /////////////////////////////////////////

  function void export_blocking_calls_helper();
      ml_tlm1_connector_base con;
      int unsigned           s;
      int unsigned           id;
      int unsigned           callback_adapter_id;
      int unsigned           stream_size;
      `STREAM_T              stream;
      int unsigned           def;

      s = active_b_put_connectors.size();

      for (int j = 0; j < s; j++) begin
          con = active_b_put_connectors.pop_front();
          callback_adapter_id = put_adapter_ids.pop_front();
          id = put_call_ids.pop_front();
          def = put_call_defs.pop_front();
          stream_size = put_stream_sizes.pop_front();
          stream = put_stream_queue.pop_front();
          if (def == `UVM_ML_TRANSPORT_DEF)
              con.export_transport_request(id, callback_adapter_id, stream_size, stream);
          else
              con.export_put_request(id, callback_adapter_id, stream_size, stream);
      end

      s = active_b_get_connectors.size();

      if (trace_mode) begin
          string msg;
          $swrite(msg, "UVM-ML SV>> In blocking_calls_helper(). active_b_get_connectors.size() = ", s);
          trace_msg(msg);
      end
      for (int j = 0; j < s; j++) begin
          con = active_b_get_connectors.pop_front();
          callback_adapter_id = get_adapter_ids.pop_front();
          id = get_call_ids.pop_front();
          def = get_call_defs.pop_front();
          if (def != `UVM_ML_TRANSPORT_DEF)
              con.export_get_object(id, callback_adapter_id, def);
      end
  endfunction : export_blocking_calls_helper

// /////////////////////////////////////////
//
// add_blocking_call_id
//
// /////////////////////////////////////////

  function blocking_call_id_class add_blocking_call_id();
      blocking_call_id_class call_id_object;

      call_id_object = new;
      call_id_object.call_id = last_blocking_call_id;
      last_blocking_call_id++;
      blocking_call_ids.push_back(call_id_object);
      return call_id_object;
  endfunction : add_blocking_call_id

// /////////////////////////////////////////
//
// remove_blocking_call_id
//
// /////////////////////////////////////////

  function void remove_blocking_call_id(int unsigned call_id);

      blocking_call_id_class call_id_object;

      foreach (blocking_call_ids[j]) begin
          call_id_object = blocking_call_ids[j];
          if (call_id_object.call_id == call_id) begin
	      blocking_call_ids.delete(j);
              break;
          end
      end
  endfunction : remove_blocking_call_id

// /////////////////////////////////////////
//
// export_notify_end_blocking
//
// /////////////////////////////////////////

  function void export_notify_end_blocking(int unsigned call_id);

      blocking_call_id_class call_id_object;

      foreach (blocking_call_ids[j]) begin
          call_id_object = blocking_call_ids[j];
          if (call_id_object.call_id == call_id) begin
              ->call_id_object.done;
               blocking_call_ids.delete(j);
               break;
          end
      end
  endfunction : export_notify_end_blocking

