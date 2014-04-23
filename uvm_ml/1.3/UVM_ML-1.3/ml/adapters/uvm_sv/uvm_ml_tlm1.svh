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

`define UVM_ML_GET_DEF       (1<<0)
`define UVM_ML_PUT_DEF       (1<<1)
`define UVM_ML_PEEK_DEF      (1<<2)
`define UVM_ML_TRANSPORT_DEF (1<<3)

typedef class blocking_call_id_class;

typedef enum { UNSPECIFIED_ML_IMP_DIRECTION, ML_IMP_PROVIDER, ML_IMP_PRODUCER} ml_imp_direction_e;

virtual class ml_tlm1_connector_base extends tlm_connector_base;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector_base::new
//
    function new (string name, uvm_component parent);
          super.new(name, parent);
     endfunction : new

    pure virtual function void export_get_object(int unsigned call_id, int unsigned callback_adapter_id, int unsigned def);
endclass : ml_tlm1_connector_base

//////////////////
//
// class uvm_ml_any_port_type
//
// This class is needed to bypass the fact that the uvm_port_base
// class is abstract and cannot be instantiated
//

class uvm_ml_any_port_type #(type T1=uvm_object, type T2=T1) extends uvm_port_base #(uvm_tlm_if_base #(T1, T2));

    int unsigned m_conn_id;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::new
//
  function new (string          name, 
                uvm_component   parent, 
                uvm_port_type_e port_type, 
                int             mask,
                int unsigned    conn_id,
                int             min_size=1, 
                int             max_size=1);
      super.new (name, parent, port_type, min_size, max_size);
      m_if_mask = mask;
      m_conn_id = conn_id;
   endfunction : new

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::try_put
//
  virtual function bit try_put(input T1 t);

      int       packed_size;
      `STREAM_T packed_stream;
      bit       result;

      if (trace_mode) begin
          string msg;
          $swrite (msg, "UVM-ML SV>> In uvm_ml_any_port_type::try_put of %s", get_full_name());
          trace_msg(msg);
      end
    
      packed_size = uvm_ml_serialization_kit::pack_cur_stream(t, packed_stream);

      return uvm_ml_nb_put(m_conn_id, packed_size, packed_stream);
  endfunction : try_put

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::can_put
//
  virtual function bit can_put();

      if (trace_mode)
          trace_msg("UVM-ML SV>> In uvm_ml_any_port_type::can_put");
    
      return uvm_ml_can_put(m_conn_id);
  endfunction : can_put

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::try_get
//
  virtual function bit try_get(output T2 t);
      int unsigned        packed_size;
      `STREAM_T           packed_stream;
      bit                 result;

      if (trace_mode)
          trace_msg("UVM-ML SV>> In uvm_ml_any_port_type::try_get");
    
      result = uvm_ml_nb_get(m_conn_id, packed_size, packed_stream);
      if (result)
          $cast(t, uvm_ml_serialization_kit::create_and_unpack_cur_stream(packed_size, packed_stream));
      else
          t = null;
      return result;
  endfunction : try_get

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::can_get
//
  virtual function bit can_get();

      if (trace_mode)
          trace_msg("UVM-ML SV>> In uvm_ml_any_port_type::can_get");
    
      can_get = uvm_ml_can_get(m_conn_id);
      return can_get;
  endfunction : can_get

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::try_peek
//
  virtual function bit try_peek(output T2 t);
      int unsigned        packed_size;
      `STREAM_T           packed_stream;
      bit                 result;

      if (trace_mode)
          trace_msg("UVM-ML SV>> In uvm_ml_any_port_type::try_peek");
    
      result = uvm_ml_nb_peek(m_conn_id, packed_size, packed_stream);
    
      if (result)
          $cast(t, uvm_ml_serialization_kit::create_and_unpack_cur_stream(packed_size, packed_stream));
      else
          t = null;
      return result;
  endfunction : try_peek

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::can_peek
//
  virtual function bit can_peek();

      if (trace_mode)
          trace_msg("UVM-ML SV>> In uvm_ml_any_port_type::can_peek");
    
      can_peek = uvm_ml_can_peek(m_conn_id);
      return can_peek;
  endfunction : can_peek

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::put
//
  virtual task put(input T1 t);
      int                    packed_size;
      `STREAM_T              packed_stream;

      blocking_call_id_class call_id_object;
      int unsigned           j;
      int unsigned           done;
      int                    request_result;

      packed_size = uvm_ml_serialization_kit::pack_cur_stream(t, packed_stream);
      call_id_object = add_blocking_call_id();
      // Must call put_request rather than put because request works both for blocking and preemptive blocking calls
      uvm_ml_put_request(m_conn_id, call_id_object.call_id, packed_size, packed_stream, done);

      if (!done) call_id_object.wait_end_blocking();
      else remove_blocking_call_id(call_id_object.call_id);
  endtask : put

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::get
//
  virtual task get(output T2 t);
      int                    packed_size;
      `STREAM_T              packed_stream;

      blocking_call_id_class call_id_object;
      int unsigned           j;
      int unsigned           done;
      int                    request_result;

      call_id_object = add_blocking_call_id();
      // Must call get_request rather than get_stream because 
      // request works both for blocking and preemptive blocking calls
      uvm_ml_get_request(m_conn_id, call_id_object.call_id, packed_size, packed_stream, done);
      if (!done) begin
          call_id_object.wait_end_blocking();
          packed_size = uvm_ml_get_requested(m_conn_id,call_id_object.call_id,packed_stream);
      end
      else remove_blocking_call_id(call_id_object.call_id);
      $cast(t, uvm_ml_serialization_kit::create_and_unpack_cur_stream(packed_size, packed_stream));
  endtask

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::peek
//
  virtual task peek(output T2 t);
      int                    packed_size;
      `STREAM_T              packed_stream;

      blocking_call_id_class call_id_object;
      int unsigned           j;
      int unsigned           done;
      int                    request_result;

      call_id_object = add_blocking_call_id();
      uvm_ml_peek_request(m_conn_id, call_id_object.call_id, packed_size, packed_stream, done);
      if (!done) begin
          call_id_object.wait_end_blocking();
          packed_size = uvm_ml_get_requested(m_conn_id,call_id_object.call_id,packed_stream);
      end
      else remove_blocking_call_id(call_id_object.call_id);
      $cast(t, uvm_ml_serialization_kit::create_and_unpack_cur_stream(packed_size, packed_stream));
  endtask : peek

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::nb_transport
//
  virtual function bit nb_transport(input T1 req, output T2 rsp);
      int              req_packed_size;
      static `STREAM_T req_packed_stream;
      int              rsp_packed_size;
      static `STREAM_T rsp_packed_stream;
      bit              result;

      req_packed_size = uvm_ml_serialization_kit::pack_cur_stream(req, req_packed_stream);

      result = uvm_ml_nb_transport(m_conn_id, req_packed_size, 
                                   req_packed_stream, rsp_packed_size, rsp_packed_stream);
      if (result)
          $cast(rsp, uvm_ml_serialization_kit::create_and_unpack_cur_stream(rsp_packed_size, rsp_packed_stream));
      else
          rsp = null;
      return result;
  endfunction : nb_transport

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::transport
//
  virtual task transport(input T1 req, output T2 rsp);
      int                    req_packed_size;
      `STREAM_T              req_packed_stream;
      int                    rsp_packed_size;
      `STREAM_T              rsp_packed_stream;

      blocking_call_id_class call_id_object;
      int unsigned           j;
      int unsigned           done;
      int                    request_result;

      call_id_object = add_blocking_call_id();
      req_packed_size = uvm_ml_serialization_kit::pack_cur_stream(req, req_packed_stream);

      uvm_ml_transport_request(m_conn_id, call_id_object.call_id, req_packed_size, 
                               req_packed_stream, rsp_packed_size, rsp_packed_stream, done);
      if (!done) begin
          call_id_object.wait_end_blocking();
          rsp_packed_size = uvm_ml_transport_response(m_conn_id,call_id_object.call_id,rsp_packed_stream);
      end
      else remove_blocking_call_id(call_id_object.call_id);
      $cast(rsp, uvm_ml_serialization_kit::create_and_unpack_cur_stream(rsp_packed_size,rsp_packed_stream));
  endtask : transport

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_any_port_type::write
//
  virtual function void write(input T1 t);
      int                 packed_size;
      `STREAM_T           packed_stream;

      packed_size = uvm_ml_serialization_kit::pack_cur_stream(t, packed_stream);

      if (trace_mode)
        trace_msg("UVM-ML SV>> In ml_tlm1_connector::write");
    
      uvm_ml_write(m_conn_id, packed_size, packed_stream);
  endfunction : write

endclass : uvm_ml_any_port_type

/////////////////////

class ml_tlm1_connector #(type T1=uvm_object, type T2=T1) extends ml_tlm1_connector_base;

    typedef uvm_port_base #(uvm_tlm_if_base #(T1, T2)) this_port_type;

    uvm_ml_any_port_type#(T1,T2) m_port;
    this_port_type               m_actual_port;
    int                          m_if_mask;
    string                       m_T1_name;
    string                       m_T2_name;
    ml_imp_direction_e           m_direction;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::new
//
  function new(this_port_type port, ml_imp_direction_e direction, string T1_name, string T2_name);

      super.new({port.get_name(), "_ml_tlm1_connector"}, port.get_parent());

      m_actual_port = port;
      m_if_mask = m_actual_port.m_get_if_mask();

      if (direction == ML_IMP_PRODUCER && port.is_imp()) begin
          `uvm_ovm_(report_fatal)("MLTLMUNKDIR", "UVM-SV adapter: Can not register a TLM imp as a ML producer");
      end
      if (direction == UNSPECIFIED_ML_IMP_DIRECTION && port.is_export()) begin
           `uvm_ovm_(report_fatal)("MLTLMUNKDIR", "UVM-SV adapter: Can not register a TLM export without explicitly specified ML direction");
      end
      if ((direction == ML_IMP_PROVIDER) || (direction == UNSPECIFIED_ML_IMP_DIRECTION && port.is_imp())) begin
          m_port = new(port.get_name(), this, UVM_PORT, port.m_get_if_mask(), m_conn_id);
          m_port.connect(port);
      end
      else begin
          m_port = new(port.get_name(), this, UVM_IMPLEMENTATION, port.m_get_if_mask(), m_conn_id);
          // Not connecting yet so that the external connection is necessary
      end

      m_T1_name = T1_name;
      m_T2_name = T2_name;
      m_direction = direction;
  endfunction : new

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_connection_name
//
  function string get_connection_name();
      string                    msg;
      //assert (m_actual_port != null);
      if(m_actual_port == null) begin
	 $swrite(msg, 
		 "UVM-SV adapter: get_connection_name cannot find the port");
	 `uvm_ovm_(report_error) ("MLTLM2CONID", msg);
	 return "";
      end;
      return m_actual_port.get_full_name();
  endfunction : get_connection_name

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_id
//
  function int unsigned get_id();
      return m_conn_id;
  endfunction : get_id

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_if_name
//
  function string get_if_name();
      case (m_if_mask)
          `uvm_ovm_TLM_(BLOCKING_PUT_MASK): get_if_name = "tlm_blocking_put";
          `uvm_ovm_TLM_(BLOCKING_GET_MASK): get_if_name = "tlm_blocking_get";
          `uvm_ovm_TLM_(BLOCKING_PEEK_MASK): get_if_name = "tlm_blocking_peek";
          `uvm_ovm_TLM_(BLOCKING_TRANSPORT_MASK): get_if_name = "tlm_blocking_transport";
          `uvm_ovm_TLM_(NONBLOCKING_PUT_MASK): get_if_name = "tlm_nonblocking_put";
          `uvm_ovm_TLM_(NONBLOCKING_GET_MASK): get_if_name = "tlm_nonblocking_get";
          `uvm_ovm_TLM_(NONBLOCKING_PEEK_MASK): get_if_name = "tlm_nonblocking_peek";
          `uvm_ovm_TLM_(NONBLOCKING_TRANSPORT_MASK): get_if_name = "tlm_nonblocking_transport";
          `uvm_ovm_TLM_(ANALYSIS_MASK): get_if_name = "tlm_analysis";
          `uvm_ovm_TLM_(PUT_MASK): get_if_name = "tlm_put";
          `uvm_ovm_TLM_(GET_MASK): get_if_name = "tlm_get";
          `uvm_ovm_TLM_(PEEK_MASK): get_if_name = "tlm_peek";
          `uvm_ovm_TLM_(BLOCKING_GET_PEEK_MASK): get_if_name = "tlm_blocking_get_peek";
          `uvm_ovm_TLM_(BLOCKING_MASTER_MASK): get_if_name = "tlm_blocking_master";
          `uvm_ovm_TLM_(BLOCKING_SLAVE_MASK): get_if_name = "tlm_blocking_slave";
          `uvm_ovm_TLM_(NONBLOCKING_GET_PEEK_MASK): get_if_name = "tlm_nonblocking_get_peek";
          `uvm_ovm_TLM_(NONBLOCKING_MASTER_MASK): get_if_name = "tlm_nonblocking_master";
          `uvm_ovm_TLM_(NONBLOCKING_SLAVE_MASK): get_if_name = "tlm_nonblocking_slave";
          `uvm_ovm_TLM_(GET_PEEK_MASK): get_if_name = "tlm_get_peek";
          `uvm_ovm_TLM_(MASTER_MASK): get_if_name = "tlm_master";
          `uvm_ovm_TLM_(SLAVE_MASK): get_if_name = "tlm_slave";
          `uvm_ovm_TLM_(TRANSPORT_MASK): get_if_name = "tlm_transport";
          default: get_if_name = "";
      endcase
  endfunction : get_if_name

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_T1_name
//
  function string get_T1_name();
      return m_T1_name;
  endfunction : get_T1_name

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_T2_name
//
  function string get_T2_name();
      return m_T2_name;
  endfunction : get_T2_name

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_type
//
  function uvm_port_type_e get_type();
      get_type = m_actual_port.is_port() ? UVM_PORT : (m_actual_port.is_export() ? UVM_EXPORT : UVM_IMPLEMENTATION);
  endfunction : get_type

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::get_actual_port_full_name
//
  function string get_actual_port_full_name();
      return m_actual_port.get_full_name();
  endfunction : get_actual_port_full_name

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::do_connect
//
// This function is internally invoked when the integrator's ml_tlm::connect()
// function is invoked. 
// Till then the if the actual port is a port it remains disconnected - 
// so that the proper error message can be issued if it is not connected 
// from another framework
//
  function void do_connect();
      if (m_actual_port.is_port() // a port always must be connected
          || m_direction == ML_IMP_PRODUCER) // an export must be connected
                                             // if it is connected to a port
          m_actual_port.connect(m_port);
  endfunction : do_connect

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::size
//
  function int unsigned size();
      return uvm_ml_get_connector_size(m_conn_id);
  endfunction : size

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_put_request
//
  function void export_put_request(int unsigned call_id, 
                                   int unsigned callback_adapter_id, 
                                   int unsigned stream_size, 
                                   `STREAM_T    stream);
      fork
          begin
              T1 arg;
              $cast(arg, uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream));
              m_actual_port.put(arg);       
              uvm_ml_notify_end_task(callback_adapter_id, call_id);
          end
      join_none
  endfunction : export_put_request

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_transport_request
//
  function void export_transport_request(int unsigned call_id, 
                                         int unsigned callback_adapter_id, 
                                         int unsigned req_stream_size, 
                                         `STREAM_T    req_stream);    
      fork
          begin
              T1 req;
              T2 rsp;
              if (trace_mode) begin
                  string msg;
                  $swrite(msg, "UVM-ML SV>> In export_transport_request. req_stream_size = %d", req_stream_size);
                  trace_msg(msg);
              end
	      $cast(req, uvm_ml_serialization_kit::create_and_unpack_cur_stream(req_stream_size, req_stream));
              m_actual_port.transport(req,rsp);
              pack_get(rsp, call_id);
              uvm_ml_notify_end_task(callback_adapter_id, call_id);
          end
      join_none
  endfunction : export_transport_request

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_try_put
//
  function bit export_try_put(int unsigned stream_size, `STREAM_T stream);
      T1 arg;
      $cast(arg, uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream));
      return m_actual_port.try_put(arg);
  endfunction : export_try_put

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_can_put
//
  function bit export_can_put();
      return m_actual_port.can_put();
  endfunction : export_can_put

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_try_get
//
  function bit export_try_get(output int unsigned stream_size, output `STREAM_T stream);
      `uvm_ovm_(object) arg;
      int        packed_size;
      bit        result;

      if (trace_mode)
          trace_msg("UVM-ML SV>> In export_try_get");
    
      result = m_actual_port.try_get(arg);

      stream_size = uvm_ml_serialization_kit::pack_cur_stream(arg, stream);
      return result;
  endfunction : export_try_get

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_can_get
//
  function bit export_can_get();
      return m_actual_port.can_get();
  endfunction : export_can_get

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_try_peek
//
  function bit export_try_peek(output int unsigned stream_size, output `STREAM_T stream);
      `uvm_ovm_(object) arg;
      bit        result;

      if (trace_mode)
          trace_msg("UVM-ML SV>> In export_try_peek");
    
      result = m_actual_port.try_peek(arg);

      stream_size = uvm_ml_serialization_kit::pack_cur_stream(arg, stream);
      return result;
  endfunction : export_try_peek

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_can_peek
//
  function bit export_can_peek();
      return m_actual_port.can_peek();
  endfunction : export_can_peek

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_get_object
//
  function void export_get_object(int unsigned call_id, int unsigned callback_adapter_id, int unsigned def);
      fork
          begin
            `uvm_ovm_(object) arg;
	    if (def == `UVM_ML_GET_DEF)
	        m_actual_port.get(arg);
            else
                m_actual_port.peek(arg);    
            pack_get(arg, call_id);
            uvm_ml_notify_end_task(callback_adapter_id, call_id);
          end
      join_none 
  endfunction : export_get_object

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_nb_transport
//
  function bit export_nb_transport(int unsigned        req_stream_size, 
                                   ref `STREAM_T       req_stream, 
                                   output int unsigned rsp_stream_size, 
                                   output `STREAM_T    rsp_stream);
      T1  req;
      T2  rsp;
      bit result;

      $cast(req, uvm_ml_serialization_kit::create_and_unpack_cur_stream(req_stream_size, req_stream));
      result = m_actual_port.nb_transport(req, rsp);
      rsp_stream_size = uvm_ml_serialization_kit::pack_cur_stream(rsp, rsp_stream);
      return result;
  endfunction : export_nb_transport

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1_connector::export_write
//
  function void export_write(int unsigned stream_size, `STREAM_T stream);

      T1 arg;
      $cast(arg, uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream));
      m_actual_port.write(arg);
  endfunction : export_write

endclass : ml_tlm1_connector

//////////////////

class ml_tlm1 #(type T1=uvm_object, type T2=T1);

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1::add_connector
//
  static function void add_connector(ml_tlm1_connector #(T1, T2) conn);
      tlm_connector_base::add_connector(conn, conn.get_actual_port_full_name());
  endfunction : add_connector

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1::register
//
  static function void register(uvm_port_base #(uvm_tlm_if_base #(T1,T2)) port, string T1_name, string T2_name);
      ml_tlm1_connector #(T1, T2) conn;
      string                      msg;

      if (trace_mode) begin
          //string msg;
          $swrite(msg, "UVM-ML SV>> In ml_tlm1::register for port %s", port.get_full_name());
          trace_msg(msg);
      end
      //assert (port.is_export() == 0); // TODO: add a new register method with a direction argument or add an optional argument here
      if(port.is_export() != 0) begin
	 $swrite(msg, 
		 "UVM-ML SV ERROR>> cannot register export");
	 `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
      end;
      conn = new (port, UNSPECIFIED_ML_IMP_DIRECTION, T1_name, T2_name);
      add_connector(conn);
  endfunction: register

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1::register_directed
//
  static function void register_directed(uvm_port_base #(uvm_tlm_if_base #(T1,T2)) port, ml_imp_direction_e direction, string T1_name, string T2_name);
      ml_tlm1_connector #(T1, T2) conn;

      if (trace_mode) begin
          string msg;
          $swrite(msg, "UVM-ML SV>> In ml_tlm1::register_directed for port %s", port.get_full_name());
          trace_msg(msg);
      end
      conn = new (port, direction, T1_name, T2_name);
      add_connector(conn);
  endfunction: register_directed

endclass : ml_tlm1
