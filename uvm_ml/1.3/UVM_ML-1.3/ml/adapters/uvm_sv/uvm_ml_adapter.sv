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

`include "uvm_ml_adapter_imp.sv"

//-------------------------------------------------
// UVM-ML SystemVerilog Adapter Package uvm_ml
// 
// This package contains only the user inreface
// The actual implementation of the adapter is
// encapsulated in package uvm_ml_adapter_imp
//-------------------------------------------------

package uvm_ml;

  import uvm_pkg::*;
//  import uvm_ml_adapter_imp::*;
  import uvm_ml_adapter_imp::`STREAM_T;
  import uvm_ml_adapter_imp::uvm_ml_tlm_gp_extensions_accessor;
    
  typedef enum { UNSPECIFIED_ML_DIRECTION, ML_PROVIDER, ML_PRODUCER} ml_direction_e;
  typedef uvm_ml_adapter_imp::uvm_ml_srv_provider_struct uvm_ml_srv_provider_struct;


// ////////////////////////////////////////////////////////////////////////////////////
//
// uvm_ml::connect() 
// uvm_ml package scope function
//
// Arguments:
// producer_name: full hierarchical name of an initiator socket(TLM2) or port (TLM1)
// provider_name: full hierarchical name of a target socket (TLM2) or export/imp (TLM1)
// map_transactions: an optional argument, relevant only for TLM2 non-blocking interface
//                   communication; This argument tells the implementation level tos
//                   re-use the transaction object if it is passed multiple times for
//                   different phases of the non-blocking TLM2 protocol. By default,
//                   the argument is not set to reduce runtime performance overhead.
// Return value: 1 - upon success, 0 - upon failure
//
//
  function bit connect(string producer_name, string provider_name, bit map_transactions = 1);
      return uvm_ml_adapter_imp::connect(producer_name, provider_name, map_transactions);
  endfunction : connect

///////////////////////////////////

  class ml_tlm2#(type TRAN_T=uvm_tlm_generic_payload, type P=uvm_tlm_phase_e);

    typedef uvm_ml_adapter_imp::ml_tlm2_register#(TRAN_T,P) tlm2_registration_t;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2#(TRAN_T,P)::register_nb_target
//
    static function void register_nb_target(uvm_tlm_nb_target_socket_base #(TRAN_T,P) sckt);
        tlm2_registration_t::nb_target(sckt);
    endfunction

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2#(TRAN_T,P)::register_nb_initiator
//
    static function void register_nb_initiator(uvm_tlm_nb_initiator_socket_base #(TRAN_T,P) sckt);
        tlm2_registration_t::nb_initiator(sckt);
    endfunction : register_nb_initiator

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2#(TRAN_T,P)::register_b_target
//
    static function void register_b_target(uvm_tlm_b_target_socket_base #(TRAN_T) sckt);
        tlm2_registration_t::b_target(sckt);
    endfunction : register_b_target

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2#(TRAN_T,P)::register_b_initiator
//
    static function void register_b_initiator(uvm_tlm_b_initiator_socket_base #(TRAN_T) sckt);
        tlm2_registration_t::b_initiator(sckt);
    endfunction : register_b_initiator

// /////////////////////////////////////////////////////////////////
//
// ml_tlm2#(TRAN_T,P)::register
//
    static function void register(uvm_port_base #(uvm_tlm_if #(TRAN_T,P)) sckt);
      if (sckt.m_get_if_mask() == `UVM_TLM_B_MASK) begin
        if (sckt.is_port()) begin
          `UVM_ML_REGISTER_B_SCKT(initiator)
        end
        else begin
          `UVM_ML_REGISTER_B_SCKT(target)
        end
      end
      else if (sckt.m_get_if_mask() == `UVM_TLM_NB_FW_MASK) begin
        if (sckt.is_port()) begin
          `UVM_ML_REGISTER_NB_SCKT(initiator)
        end
        else begin
          `UVM_ML_REGISTER_NB_SCKT(target)
        end
      end
      else begin
        `uvm_ovm_(report_fatal)("MLSCKTREG", "The argument of ml_tlm2::register() is not a supported socket");
      end
    endfunction : register
  endclass : ml_tlm2

////////////////////////////////

  class ml_tlm1 #(type T1=uvm_object, type T2=T1);

    typedef  uvm_ml_adapter_imp::ml_tlm1 #(T1, T2) tlm1_registration_t;

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1#(T1,T2)::register
//
    static function void register(uvm_port_base #(uvm_tlm_if_base #(T1,T2)) port, 
                                                  string T1_name="",
`ifdef INCA                                                  
                                                  string T2_name = T1_name
`else
                                                  string T2_name=""
`endif
);
      tlm1_registration_t::register(port, T1_name, T2_name);
    endfunction: register

// /////////////////////////////////////////////////////////////////
//
// ml_tlm1#(T1,T2)::register_directed
//
    static function void register_directed(uvm_port_base #(uvm_tlm_if_base #(T1,T2)) port,

                                                           ml_direction_e direction,

                                                           string T1_name="", 
`ifdef INCA                                                  
                                                           string T2_name = T1_name
`else
                                                           string T2_name=""
`endif
);
      tlm1_registration_t::register_directed(port, uvm_ml_adapter_imp::ml_imp_direction_e'(direction), T1_name, T2_name);
    endfunction: register_directed
  endclass : ml_tlm1

// ////////////////////////////////////////////////

  typedef class uvm_ml_class_serializer;

// /////////////////////////////////////////
//
// uvm_tlm_generic_payload serializer class
//
// /////////////////////////////////////////

  class tlm_generic_payload_serializer extends uvm_ml_class_serializer;

// /////////////////////////////////////////////////////////////////
//
// tlm_generic_payload_serializer::get_my_name
//
    function string get_my_name();
      return "uvm_tlm_generic_payload_serializer";
    endfunction : get_my_name

    uvm_tlm_generic_payload m_extensions_accessor;

    function new();
        super.new();
        m_extensions_accessor = new;
    endfunction

// /////////////////////////////////////////////////////////////////
//
// tlm_generic_payload_serializer::serialize
//
    function void serialize(uvm_object obj);
      uvm_tlm_generic_payload inst;
      int unsigned            actual_ext_num;

      $cast(inst,obj);
      pack_field_int(inst.m_address, 64);
      pack_field_int(inst.m_command, 32);

      pack_field_int(inst.m_data.size(), 32);
      foreach (inst.m_data[i]) begin
        pack_field_element(inst.m_data[i], 8);
       end

      pack_field_int(inst.m_length, 32);
      pack_field_int(inst.m_response_status, 32);

      pack_field_int(0, 32); // is_dmi_allowed
      pack_field_int(inst.m_byte_enable.size(), 32);
      foreach (inst.m_byte_enable[i]) begin
        pack_field_element(inst.m_byte_enable[i], 8);
      end
      pack_field_int(inst.m_byte_enable_length, 32);

      pack_field_int(inst.m_streaming_width, 32);

      actual_ext_num = uvm_ml_tlm_gp_extensions_accessor::get_number_of_extensions(inst);
      pack_field_int(actual_ext_num, 32);

      uvm_ml_tlm_gp_extensions_accessor::pack_extensions(inst, this);
    endfunction : serialize

// /////////////////////////////////////////////////////////////////
//
// tlm_generic_payload_serializer::deserialize
//
    function void deserialize(inout uvm_object obj);
      uvm_tlm_generic_payload inst;
      int dummy_for_is_dmi_allowed;
      int actual_ext_num;

      $cast(inst,obj);
      inst.m_address = unpack_field_int(64);
      inst.m_command = uvm_tlm_command_e'(unpack_field_int(32));

      inst.m_length = unpack_field_int(32);
      if (inst.m_length > 0) begin
        inst.m_data = new[inst.m_length];
        foreach (inst.m_data[i]) begin
          inst.m_data[i] = unpack_field_element(8);
        end
      end
      inst.m_length = unpack_field_int(32); // Do it twice - to extract the packed size and the field itself
      inst.m_response_status = uvm_tlm_response_status_e'(unpack_field_int(32));
    
      dummy_for_is_dmi_allowed = unpack_field_int(32);
    
      inst.m_byte_enable_length = unpack_field_int(32);
      if (inst.m_byte_enable_length > 0) begin
        inst.m_byte_enable = new[inst.m_byte_enable_length];
        foreach (inst.m_byte_enable[i]) begin
          inst.m_byte_enable[i] = unpack_field_element(8);
        end
      end
      inst.m_byte_enable_length = unpack_field_int(32); // Do it twice - to extract the packed size and the field itself
      inst.m_streaming_width = unpack_field_int(32);

      actual_ext_num = unpack_field_int(32);

      for (int j = 0; j < actual_ext_num; j++) begin
        uvm_tlm_extension_base ext;

        $cast(ext,unpack_field_object());
        void'(inst.set_extension(ext));
      end
    endfunction : deserialize
  endclass : tlm_generic_payload_serializer

// ///////////////////////////
//
// Package Level Functions
//
// ///////////////////////////

// /////////////////////////////////////////////////////////////////
//
// register_class_serializer
//
  function bit register_class_serializer (uvm_ml_class_serializer serializer, 
                                          uvm_object_wrapper      sv_type);
    return uvm_ml_adapter_imp::register_class_serializer (serializer, sv_type);
  endfunction : register_class_serializer

// /////////////////////////////////////////////////////////////////
//
// register_tlm_generic_payload_serializer
//
  function int register_tlm_generic_payload_serializer();
    tlm_generic_payload_serializer inst;
    inst = new;
    return register_class_serializer(inst,uvm_tlm_generic_payload::get_type());
  endfunction : register_tlm_generic_payload_serializer

  int dummy_register_tlm_generic_payload_serializer = register_tlm_generic_payload_serializer();

// /////////////////////////////////////////////////////////////////
//
// in_ml_uvm_mode (unused)
//
  function bit in_ml_uvm_mode();
    in_ml_uvm_mode = uvm_ml_adapter_imp::in_ml_uvm_mode();
  endfunction : in_ml_uvm_mode

// /////////////////////////////////////

  class uvm_ml_class_serializer extends uvm_ml_adapter_imp::uvm_ml_class_serializer;

    virtual function void serialize(uvm_object obj);
    endfunction

    virtual function void deserialize(inout uvm_object obj);
    endfunction  

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::pack_field_int
//
    function void pack_field_int (logic[63:0] value, int size);
      super.pack_field_int(value, size);
    endfunction : pack_field_int

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::pack_field
//
    function void pack_field     (uvm_bitstream_t value, int size);
      super.pack_field(value, size);
    endfunction : pack_field

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::pack_string
//
    function void pack_string    (string value);
      super.pack_string(value);
    endfunction : pack_string


// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::pack_time
//
    function void pack_time      (time value);
      super.pack_time(value);
    endfunction : pack_time

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::pack_real
//
    function void pack_real      (real value);
      super.pack_real(value);
    endfunction : pack_real

// /////////////////////////////////////
//
// uvm_ml_class_serializer::is_null
//
    function bit         is_null          ();
      return super.is_null();
    endfunction : is_null

// /////////////////////////////////////
//
// uvm_ml_class_serializer::unpack_field_int
//
    function logic[63:0] unpack_field_int (int size);
      return super.unpack_field_int(size);
    endfunction : unpack_field_int

// /////////////////////////////////////
//
// uvm_ml_class_serializer::unpack_field
//
    function uvm_bitstream_t unpack_field     (int size);
      return super.unpack_field(size);
    endfunction : unpack_field

// /////////////////////////////////////
//
// uvm_ml_class_serializer::unpack_string
//
    function string      unpack_string    (int num_chars=-1);
      return super.unpack_string(num_chars);
    endfunction : unpack_string

// /////////////////////////////////////
//
// uvm_ml_class_serializer::unpack_time
//
    function time        unpack_time      ();
      return super.unpack_time();
    endfunction : unpack_time

// /////////////////////////////////////
//
// uvm_ml_class_serializer::unpack_real
//
    function real        unpack_real      ();
      return super.unpack_real();
    endfunction : unpack_real

// /////////////////////////////////////
//
// uvm_ml_class_serializer::unpack_field_object
//
    function uvm_object  unpack_field_object();
      return super.unpack_field_object();
    endfunction : unpack_field_object

  endclass : uvm_ml_class_serializer

// /////////////////////////////////////////////////////////////////
//
// serialize_object
//
  function automatic int unsigned serialize_object(uvm_object    obj, 
                                                   ref `STREAM_T out_stream);
    return uvm_ml_adapter_imp::serialize_object(obj, out_stream);
  endfunction : serialize_object

// /////////////////////////////////////////////////////////////////
//
// deserialize_object
//
  function automatic uvm_object deserialize_object(int unsigned  stream_size,
                                                   ref `STREAM_T stream);
    return uvm_ml_adapter_imp::deserialize_object(stream_size, stream);
  endfunction : deserialize_object

// /////////////////////////////////////////////////////////////////
//
// set_type_match
//
  function int set_type_match(string type_name1, string type_name2);
    return uvm_ml_adapter_imp::set_type_match(type_name1, type_name2);
  endfunction : set_type_match


// /////////////////////////////////////////////////////////////////
//
// Task: uvm_ml_run_test
//
// Calls backplane to start environment and run test.
//
// Parameters:
//
//  tops - List of names of the top components
//  test - Name of the test component
//
  task uvm_ml_run_test(string tops[], string test = "");
     int result;
     uvm_ml_adapter_imp::uvm_ml_run_test(uvm_ml_adapter_imp::adapter_id, tops, test, result);
     if (result == 0) begin
        `uvm_ovm_(report_fatal)("MLRUNTESTF", "uvm_ml::uvm_ml_run_test() failed");
     end
  endtask : uvm_ml_run_test
        
// /////////////////////////////////////////////////////////////////
//
// Task: synchronize
//
// Calls backplane to synchronize simulation time between all frameworks.
//
  task synchronize();
      uvm_ml_adapter_imp::uvm_ml_synchronize();
  endtask : synchronize

// /////////////////////////////////////////////////////////////////
//
// Function: uvm_ml_register_srv_providers
//
// Calls backplane to register which framework will provide which service.
//
// Parameters:
//
// srv_providers - List of fields populated with name of framework providing the service.
//                 Null fields are ignored by the backplane. 
//
  function void uvm_ml_register_srv_providers(uvm_ml_adapter_imp::uvm_ml_srv_provider_struct srv_providers);
     uvm_ml_adapter_imp::uvm_ml_register_srv_providers(srv_providers);
  endfunction : uvm_ml_register_srv_providers

// /////////////////////////////////////////////////////////////////
//
// ML Hierarchy
//

function uvm_component uvm_ml_create_component(string        target_framework_indicator, 
                                               string        component_type_name, 
                                               string        instance_name,
                                               uvm_component parent = null);
    return uvm_ml_adapter_imp::create_component(target_framework_indicator, 
                                                component_type_name, instance_name, parent);
endfunction : uvm_ml_create_component

endpackage


