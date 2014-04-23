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

// /////////////////////////////////
//
// TLM2
//
// /////////////////////////////////

const int unsigned ML_TLM2_UNINITIALIZED_ID = 32'hffffffff;

// ////////////////////////////////////////////////
//
// uvm_tlm_generic_payload extensions access class
//
// ////////////////////////////////////////////////

typedef class uvm_ml_class_serializer;

class uvm_ml_tlm_gp_extensions_accessor extends uvm_tlm_generic_payload;
    static function int unsigned get_number_of_extensions (uvm_tlm_generic_payload inst);
        int unsigned actual_ext_num;
        foreach(inst.m_extensions[ext]) begin
            if (ext != null) begin
                actual_ext_num++;
            end
        end
        return actual_ext_num;
    endfunction : get_number_of_extensions

    static function void pack_extensions(uvm_tlm_generic_payload inst, 
                                         uvm_ml_class_serializer serializer);
        
        foreach(inst.m_extensions[ext_]) begin
            uvm_tlm_extension_base ext = inst.m_extensions[ext_];
            serializer.pack_object(ext); 
        end
    endfunction : pack_extensions

    static function void clone_extensions(uvm_tlm_generic_payload tx,
                                          uvm_tlm_generic_payload t);
        foreach (tx.m_extensions[ext]) begin
            $cast(t.m_extensions[ext], tx.m_extensions[ext].clone());
        end
    endfunction
endclass : uvm_ml_tlm_gp_extensions_accessor

// /////////////////////////////////
//
// Transport functor classes
//
// /////////////////////////////////

virtual class ml_tlm2_functor_base;
  pure virtual function uvm_tlm_sync_e incoming_nb_transport(ref int unsigned    stream_size, 
                                                             ref `STREAM_T       stream, 
                                                             ref uvm_tlm_phase_e p, 
                                                             int unsigned        transaction_id, 
                                                             ref uvm_tlm_time    delay);
  pure virtual function string get_socket_name();

endclass : ml_tlm2_functor_base

//////////////////

typedef class ml_tlm2_nb_connector_base;

virtual class ml_tlm2_nb_functor #(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e) extends ml_tlm2_functor_base;

  ml_tlm2_nb_connector_base m_connector;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_functor::new
//
// /////////////////////////////////////////////////////////////////

  function new(ml_tlm2_nb_connector_base conn);
      m_connector = conn;
  endfunction : new

  pure virtual function uvm_tlm_sync_e do_outgoing_nb_transport(int unsigned             conn_id, 
                                                                ref int unsigned         stream_size,
                                                                ref `STREAM_T            stream,
                                                                ref P                    p,
                                                                int unsigned             transaction_id,
                                                                inout uvm_ml_time_unit_e delay_unit,
                                                                inout real               delay_val);

  pure virtual function uvm_tlm_sync_e do_incoming_nb_transport(TRAN_T t, int unsigned transaction_id, ref P p, ref uvm_tlm_time  delay);

  pure virtual function bit do_pre_outgoing_transaction_mapping(TRAN_T t, ref int unsigned transaction_id, ref P p); 

  pure virtual function bit do_post_outgoing_transaction_mapping(TRAN_T t, ref int unsigned transaction_id, ref P p, uvm_tlm_sync_e ret); 

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_functor::outgoing_nb_transport
//
// /////////////////////////////////////////////////////////////////

  function uvm_tlm_sync_e outgoing_nb_transport(int unsigned conn_id, 
                                                string       function_name,
                                                TRAN_T       t, 
                                                ref P        p, 
                                                uvm_tlm_time delay);
      int unsigned         stream_size;
      `STREAM_T            stream;
      uvm_ml_time_unit_e  delay_unit;
      real                 delay_val;
      uvm_ml_time_unit_e  delay_unit_pre;
      real                 delay_val_pre;
      int unsigned         transaction_id;
      uvm_tlm_sync_e       sync_result;
      uvm_object           tr;
      TRAN_T               tx;

      stream_size = uvm_ml_serialization_kit::pack_cur_stream(t, stream);
      ml_tlm2_imp::from_uvm_tlm_time(delay, delay_unit, delay_val);

      delay_unit_pre = delay_unit;
      delay_val_pre = delay_val;
          
      transaction_id = ML_TLM2_UNINITIALIZED_ID;
      if (m_connector.get_transaction_mapping() != 0) begin
          if (do_pre_outgoing_transaction_mapping(t, transaction_id, p) == 0)
              return UVM_TLM_COMPLETED;
      end
          
      sync_result = do_outgoing_nb_transport(conn_id, stream_size, stream, p, transaction_id, delay_unit, delay_val);

      if (delay_unit != delay_unit_pre || delay_val != delay_val_pre)
          delay = ml_tlm2_imp::to_uvm_tlm_time(delay_unit, delay_val);

      tr = uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream);
      if (!$cast(tx, tr)) begin
          `uvm_ovm_(report_fatal) ("MLTLM2TYPM", {"UVM-SV adapter: ", function_name, " failed due to the type mismatch for socket ", get_socket_name() });
          return UVM_TLM_COMPLETED;
      end
      t.set_address(tx.get_address());
      t.set_response_status(tx.get_response_status());
      if (t.is_read()) begin
          string s = get_socket_name();
          ml_tlm2_imp::update_data_from_response(t, tx, s);
      end

      uvm_ml_tlm_gp_extensions_accessor::clone_extensions(tx, t);

      if (m_connector.get_transaction_mapping() != 0) begin
          if (do_post_outgoing_transaction_mapping(t, transaction_id, p, sync_result) == 0)
              return UVM_TLM_COMPLETED;
      end
      return sync_result;
  endfunction : outgoing_nb_transport

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_functor::incoming_nb_transport
//
// /////////////////////////////////////////////////////////////////

  virtual function uvm_tlm_sync_e incoming_nb_transport(ref int unsigned    stream_size, 
                                                        ref `STREAM_T       stream, 
                                                        ref uvm_tlm_phase_e p, 
                                                        int unsigned        transaction_id, 
                                                        ref uvm_tlm_time    delay);
      uvm_tlm_sync_e          sync_result;
      uvm_object              t;
      TRAN_T                  tx;

      t = uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream);
      if (!$cast(tx, t)) begin
          `uvm_ovm_(report_fatal) ("MLTLM2TYPM", {"UVM-SV adapter: Unpack operation failed due to the type mismatch for socket ", get_socket_name()});
          return UVM_TLM_COMPLETED;
      end
      sync_result = do_incoming_nb_transport(tx, transaction_id, p, delay);
      stream_size = uvm_ml_serialization_kit::pack_cur_stream(tx, stream);
      return sync_result;
  endfunction : incoming_nb_transport

endclass : ml_tlm2_nb_functor

//////////////////////////////////////////

class ml_tlm2_nb_transport_target_functor #(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e, type SCKT_T=int) extends ml_tlm2_nb_functor #(TRAN_T,P);

    SCKT_T                    m_socket;

// ///////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_target_functor::new
//
  function new(SCKT_T sckt, ml_tlm2_nb_connector_base conn);
      super.new(conn);
      m_socket = sckt;
  endfunction : new

// ///////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_target_functor::get_socket_name
//
  function string get_socket_name();
      return m_socket.get_full_name();
  endfunction : get_socket_name

// ///////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_target_functor::do_outgoing_nb_transport
//
  function uvm_tlm_sync_e do_outgoing_nb_transport(int unsigned             conn_id, 
                                                   ref int unsigned         stream_size,
                                                   ref `STREAM_T            stream,
                                                   ref P                    p,
                                                   int unsigned             transaction_id,
                                                   inout uvm_ml_time_unit_e delay_unit,
                                                   inout real               delay_val);
      uvm_tlm_sync_e result;

      result = uvm_ml_tlm2_nb_transport_bw(conn_id, stream_size, stream, p, transaction_id, delay_unit, delay_val);
      return result;
  endfunction : do_outgoing_nb_transport

// ///////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_target_functor::do_incoming_nb_transport
//
  function uvm_tlm_sync_e do_incoming_nb_transport(TRAN_T t, int unsigned transaction_id, ref P p, ref uvm_tlm_time delay);
       uvm_tlm_sync_e result;
       string         msg;

       if (m_connector.get_transaction_mapping() != 0) begin
           if (p == BEGIN_REQ) begin
	       if(transaction_id == ML_TLM2_UNINITIALIZED_ID) begin
		  $swrite(msg, 
			  "UVM-SV adapter: nb_transport failed because of uninitialized transaction id");
		  `uvm_ovm_(report_fatal) ("MLTLM2UNINI", msg);
		  return UVM_TLM_COMPLETED;
	       end;
               ml_tlm2_imp::map_transaction(t, transaction_id);
           end
           else if (p == END_RESP) begin
               TRAN_T                  mapped_trans;
               uvm_tlm_generic_payload tr;

               tr = ml_tlm2_imp::get_transaction_by_id(transaction_id);
               if ((tr == null) || ($cast(mapped_trans, tr) == 0)) begin
                   ml_tlm2_imp::transaction_mapping_update_error(m_connector.get_connection_name(), "nb_transport_fw", p);
                   return UVM_TLM_COMPLETED;
               end
               t = mapped_trans;
           end
       end

       result = m_socket.nb_transport_fw(t,p,delay);

       if (m_connector.get_transaction_mapping() != 0) begin
           if (p == END_RESP || result == UVM_TLM_COMPLETED) begin
               if (ml_tlm2_imp::release_transaction(t, transaction_id) == 0) begin
                   ml_tlm2_imp::transaction_mapping_release_error(m_connector.get_connection_name(), "nb_transport_fw", p, result);
               end
           end
        end
       return result;  
  endfunction : do_incoming_nb_transport

// ///////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_target_functor::do_pre_outgoing_transaction_mapping
//
  function bit do_pre_outgoing_transaction_mapping(TRAN_T t, ref int unsigned transaction_id, ref P p);
      transaction_id = ml_tlm2_imp::get_id_by_transaction(t);
      if (transaction_id == ML_TLM2_UNINITIALIZED_ID) begin
          ml_tlm2_imp::transaction_mapping_update_error(m_connector.get_connection_name(), "nb_transport_bw", p);
          return 0;
      end
      return 1;
  endfunction : do_pre_outgoing_transaction_mapping

// ///////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_target_functor::do_post_outgoing_transaction_mapping
//
  function bit do_post_outgoing_transaction_mapping(TRAN_T t, ref int unsigned transaction_id, ref P p, uvm_tlm_sync_e ret);
      return 1;
  endfunction : do_post_outgoing_transaction_mapping

endclass : ml_tlm2_nb_transport_target_functor

/////////////////

class ml_tlm2_nb_transport_initiator_functor #(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e, type SCKT_T=int) extends ml_tlm2_nb_functor #(TRAN_T,P);

    SCKT_T m_socket;

// //////////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_initiator_functor::new
//
  function new(SCKT_T sckt, ml_tlm2_nb_connector_base conn);
      super.new(conn);
      m_socket = sckt;
  endfunction : new

// //////////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_initiator_functor::get_socket_name
//
  function string get_socket_name();
      return m_socket.get_full_name();
  endfunction : get_socket_name

// //////////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_initiator_functor::do_outgoing_nb_transport
//
  function uvm_tlm_sync_e do_outgoing_nb_transport(int unsigned             conn_id, 
                                                   ref int unsigned         stream_size,
                                                   ref `STREAM_T            stream,
                                                   ref P                    p,
                                                   int unsigned             transaction_id,
                                                   inout uvm_ml_time_unit_e delay_unit,
                                                   inout real               delay_val);
      return uvm_ml_tlm2_nb_transport_fw(conn_id, stream_size, stream, p, transaction_id, delay_unit, delay_val);
  endfunction : do_outgoing_nb_transport

// //////////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_initiator_functor::do_incoming_nb_transport
//
  function uvm_tlm_sync_e do_incoming_nb_transport(TRAN_T t, int unsigned transaction_id, ref P p, ref uvm_tlm_time delay);
      uvm_tlm_sync_e result;

      if (m_connector.get_transaction_mapping() != 0) begin
          if (p == END_REQ || p == BEGIN_RESP) begin
              TRAN_T                  mapped_trans;
              uvm_tlm_generic_payload tr;

              tr = ml_tlm2_imp::get_transaction_by_id(transaction_id);
              if (tr == null || ($cast(mapped_trans, tr) == 0)) begin
                  ml_tlm2_imp::transaction_mapping_update_error(m_connector.get_connection_name(),"nb_transport_bw",p);
              end
              ml_tlm2_imp::bw_update_gp(mapped_trans, t); // update original transaction with t fields
              if (mapped_trans.is_read()) begin
                  ml_tlm2_imp::update_data_from_response(mapped_trans, t, m_connector.get_connection_name()); // copy the data as well
              end
              t = mapped_trans;
          end
      end

      result = m_socket.nb_transport_bw(t,p,delay);

      if (m_connector.get_transaction_mapping() != 0) begin
          if ((p == END_RESP) || (result == UVM_TLM_COMPLETED)) begin
              if (ml_tlm2_imp::release_transaction(t, transaction_id) == 0) begin
                  ml_tlm2_imp::transaction_mapping_release_error(m_connector.get_connection_name(),"nb_transport_bw",p,result);
              end
          end
      end
      return result;  
  endfunction : do_incoming_nb_transport

// //////////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_initiator_functor::do_pre_outgoing_transaction_mapping
//
  function bit do_pre_outgoing_transaction_mapping(TRAN_T t, ref int unsigned transaction_id, ref P p);
      if (p == BEGIN_REQ) begin
          ml_tlm2_imp::map_transaction(t, transaction_id);
      end
      else if (p == END_RESP) begin
          transaction_id = ml_tlm2_imp::get_id_by_transaction(t);
          if (transaction_id == ML_TLM2_UNINITIALIZED_ID) begin
              ml_tlm2_imp::transaction_mapping_update_error(m_connector.get_connection_name(),"nb_transport_fw",p);
              return 0;
          end
      end
      return 1;
  endfunction : do_pre_outgoing_transaction_mapping

// //////////////////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_transport_initiator_functor::do_post_outgoing_transaction_mapping
//
  function bit do_post_outgoing_transaction_mapping(TRAN_T t, ref int unsigned transaction_id, ref P p, uvm_tlm_sync_e ret);
      if (p == END_RESP || ret == UVM_TLM_COMPLETED) begin
          void'(ml_tlm2_imp::release_transaction(t, transaction_id));
      end
      return 1;
  endfunction : do_post_outgoing_transaction_mapping

endclass : ml_tlm2_nb_transport_initiator_functor

// /////////////////////////////////
//
// Connector classes
//
// /////////////////////////////////

virtual class ml_tlm2_connector_base extends tlm_connector_base;
  string       m_full_socket_name;

// /////////////////////////////////////////////
//
// ml_tlm2_connector_base::new
//
  function new(string sckt_name, uvm_component parent);
      super.new({sckt_name, "_ml_tlm2_connector"}, parent);
      m_full_socket_name = sckt_name;
  endfunction : new

// /////////////////////////////////////////////
//
// ml_tlm2_connector_base::get_connection_name
//
  function string get_connection_name();
      return m_full_socket_name;
  endfunction : get_connection_name

// ////////////////////////////////////
//
// ml_tlm2_connector_base::get_if_name
//
  function string get_if_name();
      return "TLM2";
  endfunction : get_if_name

  pure virtual function bit is_target();

  pure virtual function void do_connect();

// ////////////////////////////////////
//
// ml_tlm2_connector_base::get_type
//
  function uvm_port_type_e get_type();
      if (is_target) return UVM_IMPLEMENTATION;
      else return UVM_PORT;
  endfunction : get_type

// ////////////////////////////////////
//
// ml_tlm2_connector_base::get_T1_name
//
  function string get_T1_name();
      return ""; // TBD add pre-run base type compatibility checking for TLM2 sockets
  endfunction : get_T1_name

// ////////////////////////////////////
//
// ml_tlm2_connector_base::get_T2_name
//
  function string get_T2_name();
      return ""; // TBD add pre-run base type compatibility checking for TLM2 sockets
  endfunction : get_T2_name

endclass : ml_tlm2_connector_base

///////////////

virtual class ml_tlm2_nb_connector_base extends ml_tlm2_connector_base;

  bit m_enable_transaction_mapping;

// ///////////////////////////////
//
// ml_tlm2_nb_connector_base::new
//
  function new(string sckt_name, uvm_component parent);
    super.new(sckt_name, parent);
    m_enable_transaction_mapping = 1; // default
  endfunction : new

  pure virtual function ml_tlm2_functor_base get_functor();

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_connector_base::set_transaction_mapping
//
  function void set_transaction_mapping(bit set_value = 1);
    m_enable_transaction_mapping = set_value;
  endfunction : set_transaction_mapping

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_nb_connector_base::get_transaction_mapping
//
  function bit get_transaction_mapping();
      return m_enable_transaction_mapping;
  endfunction : get_transaction_mapping

endclass : ml_tlm2_nb_connector_base

///////////////

virtual class ml_tlm2_b_connector_base extends ml_tlm2_connector_base;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_b_target_connector#(TRAN_T)::new
//
  function new(string sckt_name, uvm_component parent);
    super.new(sckt_name, parent);
  endfunction : new

  pure virtual function int incoming_b_transport_request(int unsigned  call_id,
                                                         int unsigned  callback_adapter_id,
                                                         int unsigned  stream_size,
                                                         ref `STREAM_T stream,
                                                         uvm_tlm_time  delay);

  pure virtual function int incoming_b_transport_response(int unsigned         call_id,
                                                          output int unsigned  stream_size,
                                                          output `STREAM_T     stream);
endclass : ml_tlm2_b_connector_base

///////////////////////////////////////////

virtual class ml_tlm2_nb_target_connector_base extends ml_tlm2_nb_connector_base;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_b_target_connector_base::new
//
  function new(string sckt_name, uvm_component parent);
      super.new(sckt_name, parent);
  endfunction : new

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_b_target_connector_base::is_target
//
  function bit is_target();
      return 1;
  endfunction : is_target

  pure virtual function uvm_tlm_sync_e nb_transport_fw(ref int unsigned    stream_size, 
                                                       ref `STREAM_T       stream, 
                                                       ref uvm_tlm_phase_e p, 
                                                       int unsigned        transaction_id, 
                                                       ref uvm_tlm_time    delay);
endclass : ml_tlm2_nb_target_connector_base

////////////////////////////////////////////

class ml_tlm2_nb_target_connector #(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e) extends ml_tlm2_nb_target_connector_base;

    typedef ml_tlm2_nb_target_connector #(TRAN_T,P)                       this_connector_type;
    typedef uvm_tlm_nb_initiator_socket #(this_connector_type, TRAN_T, P) internal_socket_type;

    local uvm_tlm_nb_target_socket_base #(TRAN_T,P)                       m_orig_tsckt;
    internal_socket_type                                                  isocket;

    ml_tlm2_nb_transport_target_functor #(TRAN_T,P, internal_socket_type) m_functor;

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_target_connector#(TRAN_T,P)::new
//
  function new(uvm_tlm_nb_target_socket_base #(TRAN_T,P) sckt);
      super.new(sckt.get_full_name(), sckt.get_parent());

      m_orig_tsckt = sckt;
      isocket = new("isocket", this);
      m_functor = new (isocket, this);
  endfunction : new

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_target_connector#(TRAN_T,P)::do_connect
//
  function ml_tlm2_functor_base get_functor();
      return m_functor;
  endfunction : get_functor

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_target_connector#(TRAN_T,P)::do_connect
//
  function void do_connect();
      isocket.connect(m_orig_tsckt);
  endfunction : do_connect

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_target_connector#(TRAN_T,P)::nb_transport_fw
//
  function uvm_tlm_sync_e nb_transport_fw(ref int unsigned    stream_size, 
                                          ref `STREAM_T       stream, 
                                          ref uvm_tlm_phase_e p, 
                                          int unsigned        transaction_id, 
                                          ref uvm_tlm_time    delay);
    return m_functor.incoming_nb_transport(stream_size, stream, p, transaction_id, delay);
  endfunction : nb_transport_fw

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_target_connector#(TRAN_T,P)::nb_transport_bw
//
  virtual function uvm_tlm_sync_e nb_transport_bw(TRAN_T t, ref P p, input uvm_tlm_time delay);
      return m_functor.outgoing_nb_transport(m_conn_id, "nb_transport_bw", t, p, delay);
  endfunction : nb_transport_bw

endclass : ml_tlm2_nb_target_connector

///////////////////////////////////////////////////////////////////////////////////

virtual class ml_tlm2_nb_initiator_connector_base extends ml_tlm2_nb_connector_base;

  pure virtual function uvm_tlm_sync_e nb_transport_bw(ref int unsigned    stream_size, 
                                                       ref `STREAM_T       stream, 
                                                       ref uvm_tlm_phase_e p, 
                                                       int unsigned        transaction_id, 
                                                       ref uvm_tlm_time    delay);
// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector_base::new
//
  function new(string sckt_name, uvm_component parent);
      super.new(sckt_name, parent);
  endfunction : new

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector_base::is_target
//
  function bit is_target();
      return 0;
  endfunction : is_target

endclass : ml_tlm2_nb_initiator_connector_base

//////////////////////////////////////////////////////////////

class ml_tlm2_nb_initiator_connector #(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e) extends ml_tlm2_nb_initiator_connector_base;

    typedef ml_tlm2_nb_initiator_connector #(TRAN_T,P) this_connector_type;
    typedef uvm_tlm_nb_target_socket #(this_connector_type, TRAN_T, P) internal_socket_type;
  
    local uvm_tlm_nb_initiator_socket_base #(TRAN_T,P) m_orig_isckt;
    internal_socket_type                               tsocket;

    ml_tlm2_nb_transport_initiator_functor #(TRAN_T,P, internal_socket_type) m_functor;

// ///////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector#(TRAN_T,P)::new
//
  function new(uvm_tlm_nb_initiator_socket_base #(TRAN_T,P) sckt);
      super.new(sckt.get_full_name(), sckt.get_parent());

      m_orig_isckt = sckt;
      tsocket = new("tsocket", this);
      m_functor = new (tsocket, this);
  endfunction : new

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector#(TRAN_T,P)::get_functor
//
  function ml_tlm2_functor_base get_functor();
      return m_functor;
  endfunction : get_functor

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector#(TRAN_T,P)::do_connect
//
  function void do_connect();
      m_orig_isckt.connect(tsocket);
  endfunction : do_connect

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector#(TRAN_T,P)::nb_transport_fw
//
  function uvm_tlm_sync_e nb_transport_fw(TRAN_T t, ref P p, input uvm_tlm_time delay);

      return m_functor.outgoing_nb_transport(m_conn_id, "nb_transport_fw", t, p, delay);
  endfunction : nb_transport_fw

// ///////////////////////////////////////////////////////////
//
// ml_tlm2_nb_initiator_connector#(TRAN_T,P)::nb_transport_bw
//
  function uvm_tlm_sync_e nb_transport_bw(ref int unsigned    stream_size, 
                                          ref `STREAM_T       stream, 
                                          ref uvm_tlm_phase_e p, 
                                          int unsigned        transaction_id, 
                                          ref uvm_tlm_time    delay);
      uvm_tlm_sync_e sync_result = m_functor.incoming_nb_transport(stream_size, stream, p, transaction_id, delay);
      return sync_result;
  endfunction : nb_transport_bw
endclass : ml_tlm2_nb_initiator_connector

////////////////////////

class ml_tlm2_b_target_connector #(type TRAN_T=uvm_tlm_generic_payload) extends ml_tlm2_b_connector_base;
  typedef ml_tlm2_b_target_connector #(TRAN_T) this_connector_type;
  typedef uvm_tlm_b_initiator_socket #(TRAN_T) internal_socket_type;

  uvm_tlm_b_target_socket_base #(TRAN_T) m_orig_tsckt;
  internal_socket_type                   isocket;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_b_target_connector#(TRAN_T)::new
//
  function new(uvm_tlm_b_target_socket_base #(TRAN_T) sckt);
      super.new(sckt.get_full_name(), sckt.get_parent());
      m_orig_tsckt = sckt;
      isocket = new("isocket", this);
  endfunction : new

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2_b_target_connector#(TRAN_T)::is_target
//
  function bit is_target();
      return 1;
  endfunction : is_target

// ///////////////////////////////////////////////
//
// ml_tlm2_b_target_connector#(TRAN_T)::do_connect
//
  function void do_connect();
      isocket.connect(m_orig_tsckt);
  endfunction : do_connect

// /////////////////////////////////////////
//
// ml_tlm2_b_target_connector#(TRAN_T)::incoming_b_transport_request
//
  function int incoming_b_transport_request(int unsigned  call_id,
                                            int unsigned  callback_adapter_id,
                                            int unsigned  stream_size,
                                            ref `STREAM_T stream,
                                            uvm_tlm_time  delay);
      uvm_object   t;
      TRAN_T       tx;
      uvm_tlm_time delay_sav;

      t = uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream);
      if (!$cast(tx, t)) begin
          `uvm_ovm_(report_fatal) ("MLTLM2TYPM", {"UVM-SV adapter:  Unpack operation failed due to the type mismatch for socket ", m_orig_tsckt.get_full_name()});
          return 0;
      end

      delay_sav = delay;
      fork
      begin
          `STREAM_T stream_res;
          int unsigned stream_size_res;
          int unsigned call_id_sav;
          int unsigned callback_adapter_id_sav;

          call_id_sav = call_id;
          callback_adapter_id_sav = callback_adapter_id;
          isocket.b_transport(tx,delay_sav);
          stream_size_res = uvm_ml_serialization_kit::pack_cur_stream(tx, stream_res);
          ml_tlm2_imp::save_b_transport_return_data(call_id, stream_size_res, stream_res); // Save data for the response call
          uvm_ml_notify_end_task(callback_adapter_id_sav, call_id_sav);
       end
      join_none 
      return 0;   
  endfunction : incoming_b_transport_request

// /////////////////////////////////////////
//
// ml_tlm2_b_target_connector#(TRAN_T)::incoming_b_transport_response
//
  function int incoming_b_transport_response(int unsigned        call_id,
                                             output int unsigned stream_size,
                                             output `STREAM_T    stream);
      stream_size = ml_tlm2_imp::b_transport_return_sizes[call_id];
      stream = ml_tlm2_imp::b_transport_returns[call_id];
      return 0;
  endfunction : incoming_b_transport_response

endclass : ml_tlm2_b_target_connector

/////////////////

class ml_tlm2_b_initiator_connector #(type TRAN_T=uvm_tlm_generic_payload) extends ml_tlm2_connector_base;

  typedef ml_tlm2_b_initiator_connector #(TRAN_T)                this_connector_type;
  typedef uvm_tlm_b_target_socket #(this_connector_type, TRAN_T) internal_socket_type;

  uvm_tlm_b_initiator_socket_base #(TRAN_T) m_orig_isckt;
  internal_socket_type                      tsocket;

// /////////////////////////////////////////
//
// ml_tlm2_b_initiator_connector#(TRAN_T)::new
//
  function new(uvm_tlm_b_initiator_socket_base #(TRAN_T) sckt);
    super.new(sckt.get_full_name(), sckt.get_parent());
    m_orig_isckt = sckt;
    tsocket = new("tsocket", this);
  endfunction : new

// /////////////////////////////////////////
//
// ml_tlm2_b_initiator_connector#(TRAN_T)::is_target
//
  function bit is_target();
    return 0;
  endfunction : is_target

// /////////////////////////////////////////
//
// ml_tlm2_b_initiator_connector#(TRAN_T)::do_connect
//
  function void do_connect();
    m_orig_isckt.connect(tsocket);
  endfunction : do_connect

// /////////////////////////////////////////
//
// ml_tlm2_b_initiator_connector#(TRAN_T)::b_transport
//
  task b_transport(TRAN_T t, uvm_tlm_time delay);
      int unsigned           stream_size;
      `STREAM_T              stream;
      uvm_ml_time_unit_e     delay_unit;
      real                   delay_val;
      int                    res;
      uvm_object             tr;
      TRAN_T                 tx;
      blocking_call_id_class call_id_object;
      int unsigned           done;

      stream_size = uvm_ml_serialization_kit::pack_cur_stream(t, stream);
      ml_tlm2_imp::from_uvm_tlm_time(delay, delay_unit, delay_val);

      call_id_object = add_blocking_call_id();

      res = uvm_ml_tlm2_b_transport_request(m_conn_id, call_id_object.call_id, 
                                            stream_size, stream, delay_unit, delay_val, done);
      if (!done) begin
          call_id_object.wait_end_blocking();
          res = uvm_ml_tlm2_b_transport_response(m_conn_id, call_id_object.call_id, stream_size, stream);
      end
      else
          remove_blocking_call_id(call_id_object.call_id);
      tr = uvm_ml_serialization_kit::create_and_unpack_cur_stream(stream_size, stream);
      if (!$cast(tx, tr)) begin
          `uvm_ovm_(report_fatal) ("MLTLM2TYPM", {"UVM-SV adapter:  b_transport() failed due to the type mismatch for socket ", m_orig_isckt.get_full_name()});
          return;
      end
      t.set_address(tx.get_address());
      t.set_response_status(tx.get_response_status());
      if (t.is_read()) begin
          ml_tlm2_imp::update_data_from_response(t, tx, m_orig_isckt.get_full_name());
      end

      uvm_ml_tlm_gp_extensions_accessor::clone_extensions(tx, t);
  endtask : b_transport
endclass

int dummy_predefined_type_match1 = set_type_match("sv:uvm_pkg::uvm_tlm_generic_payload", "sc:tlm::tlm_generic_payload");

// /////////////////////////////////
//
// ML TLM2 Singleton
//
// /////////////////////////////////

class ml_tlm2_imp;

  local static ml_tlm2_nb_connector_base nb_target_socket_map[string];
  local static ml_tlm2_nb_connector_base nb_init_socket_map[string];
  local static ml_tlm2_b_connector_base  b_target_socket_map[string];
  local static ml_tlm2_connector_base    b_init_socket_map[string];

  local static uvm_tlm_generic_payload   transaction_mapping_map[int unsigned]; // map by transaction_id
  local static int unsigned              id_mapping_map[uvm_tlm_generic_payload]; // map by gp

  function new();
  endfunction

// /////////////////////////////////////////
//
// ml_tlm2_imp::add_nb_target_connector
//
  static function void add_nb_target_connector(ml_tlm2_nb_target_connector_base conn, string full_name);
      nb_target_socket_map[full_name] = conn;
      tlm_connector_base::add_connector(conn, full_name);
  endfunction : add_nb_target_connector

// /////////////////////////////////////////
//
// ml_tlm2_imp::add_nb_init_connector
//
  static function void add_nb_init_connector(ml_tlm2_nb_initiator_connector_base conn, string full_name);
      nb_init_socket_map[full_name] = conn;
      tlm_connector_base::add_connector(conn, full_name);
  endfunction : add_nb_init_connector

// /////////////////////////////////////////
//
// ml_tlm2_imp::add_b_target_connector
//
  static function void add_b_target_connector(ml_tlm2_b_connector_base conn, string full_name);
      b_target_socket_map[full_name] = conn;
      tlm_connector_base::add_connector(conn, full_name);
  endfunction : add_b_target_connector

// /////////////////////////////////////////
//
// ml_tlm2_imp::add_b_init_connector
//
  static function void add_b_init_connector(ml_tlm2_connector_base conn, string full_name);
      b_init_socket_map[full_name] = conn;
      tlm_connector_base::add_connector(conn, full_name);
  endfunction : add_b_init_connector

// /////////////////////////////////////////
//
// ml_tlm2_imp::find_tlm2_connector_by_inst_name
//
  static function int find_tlm2_connector_by_inst_name(string name);
      if (nb_target_socket_map.exists(name)) begin
          return nb_target_socket_map[name].get_id();
      end else if (nb_init_socket_map.exists(name)) begin
          return nb_init_socket_map[name].get_id();
      end else if (b_target_socket_map.exists(name)) begin
          return b_target_socket_map[name].get_id();
      end else if (b_init_socket_map.exists(name)) begin
          return b_init_socket_map[name].get_id();
      end
      return (-1);
  endfunction : find_tlm2_connector_by_inst_name

// /////////////////////////////////////////
//
// ml_tlm2_imp::scaled_time_unit
//
  static function real scaled_time_unit(uvm_ml_time_unit_e ml_unit);
      case (ml_unit)
          UVM_ML_TIME_UNIT_FS: scaled_time_unit = 1.0e-15; // 1fs
          UVM_ML_TIME_UNIT_PS: scaled_time_unit = 1.0e-12; // 1ps;
          UVM_ML_TIME_UNIT_NS: scaled_time_unit = 1.0e-9;  // 1ns;
          UVM_ML_TIME_UNIT_US: scaled_time_unit = 1.0e-6;  // 1us;
          UVM_ML_TIME_UNIT_MS: scaled_time_unit = 1.0e-3;  // 1ms;
          default scaled_time_unit = 1.0; // 1s;
      endcase
  endfunction : scaled_time_unit

// /////////////////////////////////////////
//
// ml_tlm2_imp::choose_time_scale
//
  static function uvm_ml_time_unit_e choose_time_scale(uvm_tlm_time d);
      real abstime = d.get_abstime(1e-15);
 //(1fs);
      if (abstime > 1e-9) //(1ns)
          return UVM_ML_TIME_UNIT_NS;
      else
          return UVM_ML_TIME_UNIT_FS;
  endfunction : choose_time_scale

// /////////////////////////////////////////
//
// ml_tlm2_imp::to_uvm_tlm_time
//
  static function uvm_tlm_time to_uvm_tlm_time(uvm_ml_time_unit_e delay_unit, real delay_val);
      real res = scaled_time_unit(delay_unit);
      to_uvm_tlm_time = new ("uvm_tlm_time", res);
      to_uvm_tlm_time.set_abstime(delay_val, res);
  endfunction : to_uvm_tlm_time

// /////////////////////////////////////////
//
// ml_tlm2_imp::from_uvm_tlm_time
//
  static function void from_uvm_tlm_time(uvm_tlm_time delay, output uvm_ml_time_unit_e delay_unit, output real delay_val);      
      delay_unit = choose_time_scale(delay);
      if (delay_unit == UVM_ML_TIME_UNIT_NS)
          delay_val = delay.get_realtime(1ns);
      else begin
          delay_unit = UVM_ML_TIME_UNIT_FS;
          delay_val = delay.get_realtime(1fs);
      end
  endfunction : from_uvm_tlm_time

// /////////////////////////////////////////
//
// ml_tlm2_imp::update_data_from_response
//
  static function void update_data_from_response(uvm_tlm_generic_payload trans, uvm_tlm_generic_payload response_gp, string socket_name);
      int unsigned length = response_gp.get_data_length();
      if (trans.get_data_length() != length) begin
          `uvm_ovm_(report_fatal) ("MLTLM2DLEN", {"UVM-SV adapter: ", socket_name, ": data_lengths in request and response transactions are different"});
      end
      if (length > 0) begin
          byte unsigned data[];
          response_gp.get_data(data);
          trans.set_data(data);
      end
  endfunction: update_data_from_response

  static int unsigned b_transport_return_sizes[int unsigned];
  static `STREAM_T    b_transport_returns[int unsigned];

// /////////////////////////////////////////
//
// ml_tlm2_imp::save_b_transport_return_data
//
  static function void save_b_transport_return_data(int unsigned call_id, int unsigned stream_size, `STREAM_T stream);
      b_transport_return_sizes[call_id] = stream_size;
      b_transport_returns[call_id] = stream;
  endfunction: save_b_transport_return_data

// /////////////////////////////////////////
//
// ml_tlm2_imp::incoming_call_prologue
//
  static function bit incoming_call_prologue(string                        function_name,
                                             int unsigned                  connector_id, 
                                             int unsigned                  stream_size,
                                             output ml_tlm2_connector_base connector_base,
                                             input uvm_tlm_time            delay = null,
                                             input uvm_ml_time_unit_e      delay_unit = UVM_ML_TIME_UNIT_FS,
                                             input real                    delay_value = 0.0);
      string                    msg;

      if (trace_mode) begin
          $swrite(msg, "UVM-ML SV>> In %s. Connector_id = %d Stream_size = %d", function_name, connector_id, stream_size);
          trace_msg(msg);
      end
      $cast(connector_base, tlm_connector_base::get(connector_id));
      if (connector_base == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: %s failed because no connector was found for id %d", function_name, connector_id);
          `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
          return 0;
      end

      if (delay != null && delay_unit != UVM_ML_TIME_UNIT_UNDEFINED && delay_value > 0)
          delay.set_abstime(delay_value, scaled_time_unit(delay_unit));
      return 1; // TBD: handle disabling blocking threads
  endfunction: incoming_call_prologue

// /////////////////////////////////////////
//
// ml_tlm2_imp::turn_off_transaction_mapping
//
  static function void turn_off_transaction_mapping(string socket_name);
      // default is 'on' for non-blocking interface
      if (nb_init_socket_map.exists(socket_name)) begin
          nb_init_socket_map[socket_name].set_transaction_mapping(0);
      end
      else if (nb_target_socket_map.exists(socket_name)) begin
          nb_target_socket_map[socket_name].set_transaction_mapping(0);
      end
      //end
  endfunction : turn_off_transaction_mapping

// /////////////////////////////////////////
//
// ml_tlm2_imp::assign_transaction_id
//
  static function int unsigned assign_transaction_id();
      return uvm_ml_assign_transaction_id();
  endfunction : assign_transaction_id

// /////////////////////////////////////////
//
// ml_tlm2_imp::map_transaction
//
  static function void map_transaction(uvm_tlm_generic_payload tlm_gp, ref int unsigned transaction_id);

      if (transaction_id == ML_TLM2_UNINITIALIZED_ID) begin
          transaction_id = assign_transaction_id();
      end

      transaction_mapping_map[transaction_id] = tlm_gp;
      id_mapping_map[tlm_gp] = transaction_id;
     
  endfunction : map_transaction

// /////////////////////////////////////////
//
// ml_tlm2_imp::get_transaction_by_id
//
  static function uvm_tlm_generic_payload get_transaction_by_id(int unsigned transaction_id);
      if (transaction_mapping_map.exists(transaction_id))
          return transaction_mapping_map[transaction_id];
      else
          return null;
  endfunction : get_transaction_by_id

// /////////////////////////////////////////
//
// ml_tlm2_imp::get_id_by_transaction
//
  static function int unsigned get_id_by_transaction(uvm_tlm_generic_payload tlm_gp);
      string                    msg;

      if (tlm_gp == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: get_id_by_transaction failed because of outgoing null transaction");
          `uvm_ovm_(report_fatal) ("MLTLM2NULL", msg);
          return 0;
      end
     
      if (id_mapping_map.exists(tlm_gp))
          return id_mapping_map[tlm_gp];  
      else
          return ML_TLM2_UNINITIALIZED_ID;
  endfunction : get_id_by_transaction

// /////////////////////////////////////////
//
// ml_tlm2_imp::release_transaction
//
  static function bit release_transaction(uvm_tlm_generic_payload tlm_gp, ref int unsigned transaction_id);
      bit result;
      string msg;

      if (tlm_gp == null) begin
          $swrite(msg, 
                  "UVM-SV adapter: release_transaction failed upon null transaction");
          `uvm_ovm_(report_fatal) ("MLTLM2NULL", msg);
          return 0;
      end
      if (id_mapping_map.exists(tlm_gp)) begin
          id_mapping_map.delete(tlm_gp);
      end
      else
          return 0;

      if (transaction_mapping_map.exists(transaction_id)) begin
          transaction_mapping_map.delete(transaction_id);
      end
      else
          return 0;

      transaction_id = ML_TLM2_UNINITIALIZED_ID;
      return 1;
  endfunction : release_transaction

// /////////////////////////////////////////
//
// ml_tlm2_imp::phase_to_string
//
  static function string phase_to_string(uvm_tlm_phase_e phase);
      case (phase)
          BEGIN_REQ: phase_to_string = "BEGIN_REQ";
          END_REQ: phase_to_string = "END_REQ";
          BEGIN_RESP: phase_to_string = "BEGIN_RESP";
          END_RESP: phase_to_string = "END_RESP";
          default phase_to_string = "invalid phase";
      endcase
  endfunction : phase_to_string

// /////////////////////////////////////////
//
// ml_tlm2_imp::status_to_string
//
  static function string status_to_string(uvm_tlm_sync_e stat);
      case (stat)
          UVM_TLM_ACCEPTED: status_to_string = "UVM_TLM_ACCEPTED";
          UVM_TLM_UPDATED: status_to_string = "UVM_TLM_UPDATED";
          UVM_TLM_COMPLETED: status_to_string = "UVM_TLM_COMPLETED";
      endcase
  endfunction : status_to_string

// /////////////////////////////////////////
//
// ml_tlm2_imp::transaction_mapping_update_error
//
  static function void transaction_mapping_update_error(string socket_name, string intf_name, uvm_tlm_phase_e phase);
      `uvm_ovm_(report_fatal)("MLTLM2TRMAPUP", {"UVM-SV adapter: ML-TLM2 non-blocking transaction did not follow the rules of the TLM2 standard.", intf_name, " of ", socket_name, " was called with phase ", phase_to_string(phase), " , but the transaction was not first sent on the forward path with the BEGIN_REQ phase, or has already returned on the forward path with the END_RESP phase or the TLM_COMPLETED status."});
  endfunction : transaction_mapping_update_error

// /////////////////////////////////////////
//
// ml_tlm2_imp::transaction_mapping_release_error
//
  static function void transaction_mapping_release_error(string socket_name, string intf_name, uvm_tlm_phase_e phase, uvm_tlm_sync_e ret);
      `uvm_ovm_(report_fatal)("MLTLM2TRMAPREL", {"UVM-SV adapter: ML-TLM2 non-blocking transaction did not follow the rules of the TLM2 standard.", intf_name, " of ", socket_name, " returned with phase ", phase_to_string(phase), " and status ", status_to_string(ret), ", but the transaction was not first sent on the forward path with the BEGIN_REQ phase, or has already returned on the forward path with the END_RESP phase or the TLM_COMPLETED status."});
  endfunction : transaction_mapping_release_error

// /////////////////////////////////////////
//
// ml_tlm2_imp::bw_update_gp
//
  static function void bw_update_gp(uvm_tlm_generic_payload tlm_gp, uvm_tlm_generic_payload other);
      tlm_gp.do_copy(other);
      tlm_gp.set_response_status(other.get_response_status()); // do_copy() does not update m_response_status
  endfunction : bw_update_gp

endclass : ml_tlm2_imp

// /////////////////////////////////
//
// Connector registration classes
//
// /////////////////////////////////

class ml_tlm2_register#(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e);

// /////////////////////////////////////////
//
// ml_tlm2_register#(TRAN_T,P)::nb_target
//
  static function void nb_target(uvm_tlm_nb_target_socket_base #(TRAN_T,P) sckt);
      ml_tlm2_nb_target_connector #(TRAN_T,P) conn = new (sckt);
      ml_tlm2_imp::add_nb_target_connector(conn, sckt.get_full_name());
  endfunction : nb_target

// /////////////////////////////////////////
//
// ml_tlm2_register#(TRAN_T,P)::nb_initiator
//
  static function void nb_initiator(uvm_tlm_nb_initiator_socket_base #(TRAN_T,P) sckt);
      ml_tlm2_nb_initiator_connector #(TRAN_T,P) conn = new (sckt);
      ml_tlm2_imp::add_nb_init_connector(conn, sckt.get_full_name());
  endfunction : nb_initiator

// /////////////////////////////////////////
//
// ml_tlm2_register#(TRAN_T,P)::b_target
//
  static function void b_target(uvm_tlm_b_target_socket_base #(TRAN_T) sckt);
      ml_tlm2_b_target_connector #(TRAN_T) conn = new (sckt);
      ml_tlm2_imp::add_b_target_connector(conn, sckt.get_full_name());
  endfunction : b_target

// /////////////////////////////////////////
//
// ml_tlm2_register#(TRAN_T,P)::b_initiator
//
  static function void b_initiator(uvm_tlm_b_initiator_socket_base #(TRAN_T) sckt);
      ml_tlm2_b_initiator_connector #(TRAN_T) conn = new (sckt);
      ml_tlm2_imp::add_b_init_connector(conn, sckt.get_full_name());
  endfunction : b_initiator
endclass : ml_tlm2_register

// /////////////////////////////////
//
// DPI export function implementations
//
// /////////////////////////////////

// /////////////////////////////////////////
//
// export_tlm2_nb_transport_incoming
//
function uvm_tlm_sync_e export_tlm2_nb_transport_incoming(int unsigned             connector_id, 
                                                          inout int unsigned       stream_size,
                                                          inout `STREAM_T          stream,
                                                          inout uvm_tlm_phase_e    phase,
                                                          input int unsigned       transaction_id,
                                                          inout uvm_ml_time_unit_e delay_unit,
                                                          inout real               delay_value);
    uvm_tlm_sync_e            sync_result;
    uvm_tlm_time              d;
    string                    msg;
    ml_tlm2_connector_base    connector_base;
    ml_tlm2_nb_connector_base connector;
    ml_tlm2_functor_base      functor;

    if (trace_mode) begin
        $swrite(msg, "UVM-ML SV>> In export_tlm2_nb_transport_incoming. Connector_id = %d Stream_size = %d", 
                connector_id, stream_size);
        trace_msg(msg);
    end
    if(stream_size <= 0) begin
       $swrite(msg, 
               "UVM-SV adapter: nb_transport failed because of empty stream");
       `uvm_ovm_(report_fatal) ("MLTLM2EMPTY", msg);
       return UVM_TLM_COMPLETED;
    end;	      
    $cast(connector_base, tlm_connector_base::get(connector_id));
    if (connector_base == null) begin
        $swrite(msg, 
                "UVM-SV adapter: export_tlm2_nb_transport_incoming failed because no connector was found for id %d", 
                connector_id);
        `uvm_ovm_(report_fatal) ("MLTLM2CONID", msg);
        return UVM_TLM_COMPLETED;
    end
    $cast(connector, connector_base);

    d = new;
    if (delay_unit != UVM_ML_TIME_UNIT_UNDEFINED && delay_value > 0)
        d.set_abstime(delay_value, ml_tlm2_imp::scaled_time_unit(delay_unit));

    functor = connector.get_functor();
    sync_result = functor.incoming_nb_transport(stream_size, stream, phase, transaction_id, d);

    if (delay_unit != UVM_ML_TIME_UNIT_UNDEFINED)
        delay_value = d.get_abstime(ml_tlm2_imp::scaled_time_unit(delay_unit));

    return sync_result;
endfunction : export_tlm2_nb_transport_incoming

// /////////////////////////////////////////
//
// export_tlm2_b_transport_request
//
function int export_tlm2_b_transport_request(int unsigned        connector_id,
                                             int unsigned        call_id,
                                             int unsigned        callback_adapter_id,
                                             int unsigned        stream_size,
                                             `STREAM_T           stream,
                                             uvm_ml_time_unit_e delay_unit,
                                             real                delay_value);
    int                       result;
    uvm_tlm_time              d;
    ml_tlm2_connector_base    connector_base;
    ml_tlm2_b_connector_base  connector;
    string                    msg;

    if(stream_size <= 0) begin
       $swrite(msg, 
               "UVM-SV adapter: export_tlm2_b_transport_request() failed because of empty incoming stream for connector id %d", connector_id);
       `uvm_ovm_(report_fatal) ("MLTLM2EMPTY", msg);
       return 0;
    end;	      

    d = new;
    result = ml_tlm2_imp::incoming_call_prologue("export_tlm2_b_transport_request", connector_id, 
                                             stream_size, connector_base, d, delay_unit, delay_value);
    if (result == 0)
        return result;

    $cast(connector, connector_base);
    return connector.incoming_b_transport_request(call_id, callback_adapter_id, stream_size, stream, d);
endfunction : export_tlm2_b_transport_request

// /////////////////////////////////////////
//
// export_tlm2_b_transport_response
//
function int export_tlm2_b_transport_response(int unsigned        connector_id,
                                              int unsigned        call_id,
                                              inout int unsigned  stream_size,
                                              output `STREAM_T    stream);
    int                       result;
    ml_tlm2_connector_base    connector_base;
    ml_tlm2_b_connector_base  connector;

    result = ml_tlm2_imp::incoming_call_prologue("export_tlm2_b_transport_response", connector_id, stream_size, connector_base);
    if (result == 0)
        return result;

    $cast(connector, connector_base);
    return connector.incoming_b_transport_response(call_id, stream_size, stream);
endfunction : export_tlm2_b_transport_response

// /////////////////////////////////////////
//
// export_tlm2_turn_off_transaction_mapping
//
function void export_tlm2_turn_off_transaction_mapping (string socket_name);
  ml_tlm2_imp::turn_off_transaction_mapping (socket_name);
endfunction : export_tlm2_turn_off_transaction_mapping
