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
// UVM/OVM object serialization facilities
//
//------------------------------------

typedef class uvm_ml_packer_base;
typedef class ml_tlm2_imp;

///////////////////////////////////////////////////////
// Class uvm_ml_serialization_kit
// contains predefined packing utilities
///////////////////////////////////////////////////////

class uvm_ml_serialization_kit;

    static uvm_ml_packer_base        m_object_serializers[`uvm_ovm_(object_wrapper)];
    static int                       m_uni_type_ids[`uvm_ovm_(object_wrapper)];
    static `uvm_ovm_(object_wrapper) m_types[int];
    static uvm_ml_packer_base        m_last_packer = null;

// uvm_ml_serialization_kit::get_uni_type_id
// ------------------------------------------

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::get_uni_type_id
//
  static function int get_uni_type_id(`uvm_ovm_(object_wrapper) sv_type, string typenm);
      int id;

      if (m_uni_type_ids.exists(sv_type))
          id = m_uni_type_ids[sv_type];
      else begin
          id = uvm_ml_get_type_id_from_name(typenm);
          // TBD: Add an error if returns an error ...
          m_uni_type_ids[sv_type] = id;
          m_types[id] = sv_type;
      end
      return id;
  endfunction : get_uni_type_id

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::get_type_by_uni_id
//
  static function `uvm_ovm_(object_wrapper) get_type_by_uni_id(int uni_type_id);
      `uvm_ovm_(object_wrapper) sv_type;
      if (m_types.exists(uni_type_id))
          sv_type = m_types[uni_type_id];
      else begin
          string typenm = uvm_ml_get_type_name_from_id(uni_type_id);
          if (factory.is_type_name_registered (typenm))
              sv_type = factory.find_by_name(typenm);
          if (sv_type != null) begin
              m_uni_type_ids[sv_type] = uni_type_id;
              m_types[uni_type_id] = sv_type;
          end
      end
      return sv_type;
  endfunction : get_type_by_uni_id

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::get_actual_packer_for_type
//
  static function uvm_ml_packer_base get_actual_packer_for_type(`uvm_ovm_(object_wrapper) sv_type);
    
      uvm_ml_packer_base packer;

      if (m_last_packer != null && (sv_type == m_last_packer.m_last_type))
          return m_last_packer;

      if (m_object_serializers.exists(sv_type)) begin
          packer = m_object_serializers[sv_type];
      end
      else begin
          packer = uvm_ml_packer;
      end
      return packer;
  endfunction : get_actual_packer_for_type

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::marshall_top_object
//
  static function uvm_ml_packer_base marshall_top_object (`uvm_ovm_(object) obj);

      uvm_ml_packer_base actual_packer;

      if (obj == null)
          actual_packer = uvm_ml_packer;
      else begin
          `uvm_ovm_(object_wrapper) sv_type = obj.get_object_type();

          actual_packer = get_actual_packer_for_type(sv_type);
          m_last_packer = actual_packer;
      end
      actual_packer.marshall_top_object(obj);
      return actual_packer;
  endfunction : marshall_top_object

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::get_sv_type_by_uni_type_id
//
  static function `uvm_ovm_(object_wrapper) get_sv_type_by_uni_type_id(int uni_type_id);
      `uvm_ovm_(object_wrapper) sv_type = (m_last_packer != null) ? m_last_packer.serves_uni_type_id(uni_type_id) : null;
      if (sv_type == null)
          sv_type = get_type_by_uni_id(uni_type_id);
    
      if(sv_type == null) begin
          string typenm = uvm_ml_get_type_name_from_id(uni_type_id);
      
          `uvm_ovm_(report_fatal)("UNKNNM", 
                                  {"The class type ", typenm, " can not be created because the UVM/OVM factory does not have the type registered."}); // TBD: Improve error message
      end
      return sv_type;
  endfunction : get_sv_type_by_uni_type_id

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::get_packer_by_uni_type_id
//
  static function uvm_ml_packer_base get_packer_by_uni_type_id(int uni_type_id);
      if (m_last_packer && (m_last_packer.serves_uni_type_id(uni_type_id) != null))
          return m_last_packer;
      else begin
          `uvm_ovm_(object_wrapper) sv_type = get_type_by_uni_id(uni_type_id);
          if (sv_type == null)
              return null;
          return get_actual_packer_for_type (sv_type);
      end
  endfunction : get_packer_by_uni_type_id

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::unmarshall_top_object
//
  static function `uvm_ovm_(object) unmarshall_top_object(int unsigned  stream_int_size,
                                                          ref `STREAM_T stream);
      uvm_ml_packer_base actual_packer;

      if (m_is_null_stream(stream))
          return null;

      if (stream_int_size < 2) begin
          `uvm_ovm_(report_fatal)("MLSHORTSTREAM", "Corrupted incoming ML stream");
          return null;
      end

      actual_packer = m_get_actual_packer_for_stream(stream);
      if (actual_packer == null) begin
         `uvm_ovm_(report_fatal)("MLTYPID", "Bad type id in the incoming ML stream");
          return null;
      end
      m_last_packer = actual_packer;
      return actual_packer.unmarshall_top_object(stream_int_size, stream);
  endfunction : unmarshall_top_object

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::is_registered_object_type
//
  static function bit is_registered_object_type(int unsigned  stream_size,
                                                ref `STREAM_T stream);
    
      uvm_ml_packer_base actual_packer;

      if ((stream_size < 2) || m_is_null_stream(stream)) begin
          return 0;
      end

      actual_packer = m_get_actual_packer_for_stream(stream);
      return (actual_packer != null);
  endfunction : is_registered_object_type

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::pack_cur_stream
//
  static function int pack_cur_stream(`uvm_ovm_(object) obj, output `STREAM_T stream);
      int size;

      uvm_ml_packer_base actual_packer = marshall_top_object(obj);
      stream = actual_packer.get_packed_internals();
      size = actual_packer.get_packed_size();
      if (size > `MAX_STREAM_SIZE) begin
          string msg;
          $swrite(msg, "Packed ML UVM/OVM transaction size %d (integers) exceeded maximal stream size %d", size, `MAX_STREAM_SIZE);
          `uvm_ovm_(report_fatal)("XMAXSTRSZ", msg);
      end

      return size * 32; // STREAMSIZE: Switching to bit size on the Backplane APi level
  endfunction : pack_cur_stream

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::create_and_unpack_cur_stream
//
  static function `uvm_ovm_(object) create_and_unpack_cur_stream(int unsigned  stream_size,
                                                                 ref `STREAM_T stream);
      int unsigned      int_size;

      uvm_ml_stream_kind_e stream_kind = uvm_ml_stream_kind_e'(stream[0]);

      if (stream_kind == UVM_ML_STREAM_RAW)
        `uvm_ovm_(report_fatal)("MLSTREAMKIND", "Wrong UVM-ML packed stream kind: expected an uvm_object but received an untyped raw stream");
      if (stream_kind == UVM_ML_STREAM_STRING)
        `uvm_ovm_(report_fatal)("MLSTREAMKIND", "Wrong UVM-ML packed stream kind: expected an uvm_object but received a string");

      int_size = stream_size/32; // STREAMSIZE: Switching to bit size on the Backplane APi level
      return unmarshall_top_object(int_size, stream);
  endfunction : create_and_unpack_cur_stream
  
// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::register_class_serializer
//
  static function bit register_class_serializer(uvm_ml_packer_base       serializer, 
                                                `uvm_ovm_(object_wrapper) sv_type);
      bit result = 1;
      if (serializer == null) begin
          result = 0;
          `uvm_ovm_(report_fatal)("NULLSRR", "Attempting to register a null class serializer with ML UVM/OVM serialization kit");
      end
      if (sv_type == null) begin
          result = 0;
          `uvm_ovm_(report_fatal)("NULLSRR", "Attempting to register a null object type wrapper with ML UVM/OVM serialization kit");
      end
      if (m_object_serializers.exists(sv_type)) begin
          if (sv_type.get_type_name() != "" && sv_type.get_type_name() != "<unknown>")
              result = 0;
          `uvm_ovm_(report_warning)("TPRGED", {"Object type '",sv_type.get_type_name(),
                                               "' already registered with serialization registry"});
      end
      else 
          m_object_serializers[sv_type] = serializer;
      return result;
  endfunction : register_class_serializer

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::initialize
//
  static function void initialize();
      `uvm_ovm_(object_wrapper) sv_type;

      // Update all previously registered serializers
      if (m_object_serializers.first(sv_type))
      do
          m_object_serializers[sv_type].set_type_marshall_imp();
      while (m_object_serializers.next(sv_type));
  endfunction : initialize

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::m_is_null_stream
//
  static function bit m_is_null_stream(ref uvm_ml_intstream_t stream);
      int is_null = stream[0];
      return (is_null == 0);
  endfunction : m_is_null_stream

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::m_get_actual_packer_for_stream
//
  static function uvm_ml_packer_base m_get_actual_packer_for_stream (ref uvm_ml_intstream_t stream);
      `uvm_ovm_(object_wrapper) sv_type;
      int uni_type_id;

      if (m_is_null_stream(stream))
          return null;

      uni_type_id = stream [1];

      m_get_actual_packer_for_stream = get_packer_by_uni_type_id(uni_type_id);
  endfunction : m_get_actual_packer_for_stream

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::pack_top_string
//
  static function int pack_top_string(string            val,
                                      output `STREAM_T stream);

      int size;

      uvm_ml_packer.pack_top_string(val);
      stream = uvm_ml_packer.get_packed_internals();
      size = uvm_ml_packer.get_packed_size();
      if (size > `MAX_STREAM_SIZE) begin
          string msg;
          $swrite(msg, "Packed ML UVM/OVM string size %d (integers) exceeded maximal stream size %d", size, `MAX_STREAM_SIZE);
          `uvm_ovm_(report_fatal)("XMAXSTRSZ", msg);
      end
      return size * 32; // STREAMSIZE: Switching to bit size on the Backplane APi level

  endfunction : pack_top_string

// /////////////////////////////////////////
//
// uvm_ml_serialization_kit::unpack_top_string
//
  static function string unpack_top_string(int unsigned  stream_size,
                                           ref `STREAM_T stream);
      int kind;
      // Accept only the null-terminated strings
      uvm_ml_packer.m_put_packed_ints(stream_size, stream);
      kind = uvm_ml_packer.unpack_field_int(32);
      return uvm_ml_packer.m_unpack_string(-1);
  endfunction : unpack_top_string

endclass : uvm_ml_serialization_kit

///////////////////////////

virtual class uvm_ml_type_marshall_base;

  uvm_ml_packer_base m_master_packer;

// /////////////////////////////////////////
//
// uvm_ml_type_marshall_base::new
//
  function new(uvm_ml_packer_base packer);
    m_master_packer = packer;
  endfunction : new

  pure virtual function void v_add_type_identifier(`uvm_ovm_(object) obj);

  pure virtual function `uvm_ovm_(object) v_create_object();

  pure virtual function `uvm_ovm_(object_wrapper) v_serves_uni_type_id(int uni_type_id);

  pure virtual function void v_cache_uni_type_id(int uni_type_id);

endclass : uvm_ml_type_marshall_base

//////////////

class uvm_ml_class_id_marshall extends uvm_ml_type_marshall_base;

    int                m_last_uni_type_id;

// /////////////////////////////////////////
//
// uvm_ml_class_id_marshall::new
//
  function new(uvm_ml_packer_base packer); 
      super.new(packer);
      m_last_uni_type_id = -1;
  endfunction : new

// /////////////////////////////////////////
//
// uvm_ml_class_id_marshall::v_add_type_identifier
//
  function void v_add_type_identifier(`uvm_ovm_(object) obj);
      `uvm_ovm_(object_wrapper) sv_type;

      sv_type = obj.get_object_type();
      if (sv_type != m_master_packer.m_last_type) begin
          m_master_packer.m_last_type = sv_type;
          m_last_uni_type_id = uvm_ml_serialization_kit::get_uni_type_id(sv_type, obj.get_type_name());
      end
      // The rest of the global fields must be already updated before this
      m_master_packer.pack_field_int(m_last_uni_type_id, 32);
  endfunction : v_add_type_identifier

// /////////////////////////////////////////
//
// uvm_ml_class_id_marshall::v_create_object
//
  function `uvm_ovm_(object) v_create_object();
      `uvm_ovm_(object)          obj;
      `uvm_ovm_(object_wrapper)  sv_type;
      uvm_ml_packer_base         object_packer;

      int uni_type_id = m_master_packer.unpack_field_int(32);

      sv_type = uvm_ml_serialization_kit::get_sv_type_by_uni_type_id(uni_type_id);
      obj = sv_type.create_object("");
      object_packer = uvm_ml_serialization_kit::get_actual_packer_for_type(sv_type);
      object_packer.m_last_type = sv_type;
      object_packer.m_type_marshall_imp.v_cache_uni_type_id(uni_type_id);
      return obj;
  endfunction : v_create_object
  
// /////////////////////////////////////////
//
// uvm_ml_class_id_marshall::v_serves_uni_type_id
//
  function `uvm_ovm_(object_wrapper) v_serves_uni_type_id(int uni_type_id);
      if (m_last_uni_type_id == uni_type_id)
          return m_master_packer.m_last_type;
      else
          return null;
  endfunction : v_serves_uni_type_id

// /////////////////////////////////////////
//
// uvm_ml_class_id_marshall::v_cache_uni_type_id
//
  virtual function void v_cache_uni_type_id(int uni_type_id);
      m_last_uni_type_id = uni_type_id;
  endfunction : v_cache_uni_type_id

endclass : uvm_ml_class_id_marshall

///////////////////////////////

virtual class uvm_ml_packer_base extends `uvm_ovm_(packer);

    uvm_ml_type_marshall_base m_type_marshall_imp;
    uvm_ml_packer_base        master_packer;
    `uvm_ovm_(object_wrapper) m_last_type;

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::set_type_marshall_imp
//
  function void set_type_marshall_imp();
      uvm_ml_class_id_marshall imp = new(this);
      m_type_marshall_imp = imp;
  endfunction : set_type_marshall_imp

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::v_marshall_object
//
  virtual function void v_marshall_object(`uvm_ovm_(object) obj);
  endfunction : v_marshall_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::v_unmarshall_object
//
  virtual function void v_unmarshall_object(inout `uvm_ovm_(object) obj);
  endfunction : v_unmarshall_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::set_master_packer
//
  function void set_master_packer(uvm_ml_packer_base packer);
    master_packer = packer;
  endfunction : set_master_packer

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_object
//
  function void pack_object (`uvm_ovm_(object) value);
      `uvm_ovm_(object_wrapper) sv_type;
      uvm_ml_packer_base nested_packer;
      uvm_ml_packer_base prev_master_packer;
     
      if (value == null) begin
          master_packer.m_pack_object(value, master_packer);
          return;
      end
      sv_type = value.get_object_type();
      nested_packer = uvm_ml_serialization_kit::get_actual_packer_for_type(sv_type);
      prev_master_packer = nested_packer.master_packer;

      uvm_ml_serialization_kit::m_last_packer = nested_packer;

      nested_packer.set_master_packer(master_packer);
      master_packer.m_pack_object(value, nested_packer);
      nested_packer.set_master_packer(prev_master_packer);
  endfunction : pack_object
  
// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::marshall_top_object
//
  function void marshall_top_object(`uvm_ovm_(object) obj);

      clear();
      uvm_object::__m_uvm_status_container.packer = this;
      m_pack_object(obj, this);
      set_packed_size();
  endfunction : marshall_top_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_object_cdns
//
  function void unpack_object_cdns (inout `uvm_ovm_(object) value);
      master_packer.m_unpack_object(value);
  endfunction : unpack_object_cdns 

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_object_ext
//
  function void unpack_object_ext (inout `uvm_ovm_(object) value);
      master_packer.m_unpack_object(value);
  endfunction : unpack_object_ext

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_field_object
//
  function `uvm_ovm_(object) unpack_field_object();
      `uvm_ovm_(object) result;
      master_packer.m_unpack_object(result);
      return result;
  endfunction : unpack_field_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::serves_uni_type_id(
//
  function `uvm_ovm_(object_wrapper) serves_uni_type_id(int uni_type_id);
      return m_type_marshall_imp.v_serves_uni_type_id(uni_type_id);
  endfunction : serves_uni_type_id

    uvm_ml_intstream_t m_ints = 0;
    int                m_packed_int_size  = 0;
    int unsigned       m_bit_count = 0;
    local bit          m_fast_object_stack[`uvm_ovm_(void)];

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::new
//
 function new(); 
    super.new(); 
    big_endian = 0;
    use_metadata = 1; 
    set_type_marshall_imp();
    master_packer = this; // Default
  endfunction : new

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_pack_field
//
  function void m_pack_field(`uvm_ovm_(bitstream_t) value, int size);
      int len;

      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      len = (size +31)/32;

      // copy len ints, even if scalar is not aligned to 32 bit
      // in order to preserve sign externsion when passing negative longs
      for (int i=0; i<len; i++) begin
          m_ints[count] = value[(i*32) +:32];
          count += 1;
      end     
  endfunction : m_pack_field

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_pack_field_element
//
  function void m_pack_field_element(logic[63:0] value, int size);
      if (size != 1)
          m_pack_field(value, size);
      else begin
          if (m_bit_count == 32) begin
              count += 1;
              m_bit_count = 0;
          end
          m_ints[count][m_bit_count] = value[0];
          m_bit_count += 1;
      end
  endfunction : m_pack_field_element

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_field
//
  function void pack_field(`uvm_ovm_(bitstream_t) value, int size);
      if (master_packer != this)
          master_packer.pack_field(value, size);
      else
          m_pack_field(value, size);
  endfunction : pack_field

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_field_element
//
  function void pack_field_element (logic[63:0] value, int size);
    if (master_packer != this)
      master_packer.pack_field_element(value, size);
    else
      m_pack_field_element(value, size);
  endfunction : pack_field_element

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_pack_field_int
//
  function void m_pack_field_int(logic [63:0] value, int size);
      int len;

      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      if (size == 32 || (size == 64)) begin // Optimize most useful constant sizes - cannot use variable in bit select
          m_ints[count] = value[31:0];
          count += 1;
          if (size == 64) begin
              m_ints[count] = value[63:32];
              count += 1;
          end 
      end
      else begin
          int len;

          len = (size+31)/32;
  
          // copy len ints, even if scalar is not aligned to 32 bit
          // in order to preserve sign externsion when passing negative longs
          for (int i=0; i<len; i++) begin
              m_ints[count] = value[(i*32) +:32];
              count += 1;
          end
      end
  endfunction : m_pack_field_int

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_field_int
//
  function void pack_field_int (logic [63:0] value, int size);
      if (master_packer != this)
          master_packer.pack_field_int(value, size);
      else
          m_pack_field_int(value, size);
  endfunction : pack_field_int

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_pack_string
//
  function void m_pack_string(string value);
      bit [3:0][7:0] bytes;
      int len;
      int rest;

      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      len = (value.len()+1)/4;    // Integers (Including the terminating character)
      rest = (value.len()+1) % 4; // Bytes

      for (int i=0; i< len; i++) begin
          for (int j = 0; j < 4; j++) begin
              bytes[j] = value[(i * 4) + j];
          end
          m_ints[count] = bytes;
          count += 1;
      end

      if (rest > 0) begin
          bytes = 0;
          for (int j = 0; j < rest; j++) begin
              bytes[j] = value[(len*4) + j];
          end
          m_ints[count] = bytes;
          count += 1;
      end
  endfunction : m_pack_string

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_string
//
  function void pack_string(string value);
    if (master_packer != this)
      master_packer.pack_string(value);
    else
      m_pack_string(value);
  endfunction : pack_string

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_time
//
  function void pack_time      (time value);
    if (master_packer != this)
      master_packer.pack_time(value);
    else
      super.pack_time(value);
  endfunction : pack_time

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_real
//
  function void pack_real(real value);
    if (master_packer != this)
      master_packer.pack_real(value);
    else
      super.pack_real(value);
  endfunction : pack_real

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::is_null
//
  function bit is_null();
      if (master_packer != this)
          return master_packer.is_null();
      else
          return (m_ints[count] == 0);
  endfunction : is_null

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_unpack_field_int
//
  function logic[63:0] m_unpack_field_int(int size);
      m_unpack_field_int = 'b0;
      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      if (enough_ints(((size-1)/32)+1,"integral")) begin
          int len;
          int rest;

          len = size/32;  // ints
          rest = size%32; // bits
          for (int i=0; i<len; i++) begin
              m_unpack_field_int[(i*32)+:32] = m_ints[count];
              count += 1;
          end
          if (rest > 0) begin
              bit [31:0] tmp;
              tmp = m_ints[count];
              count += 1;
              for (int i=0; i<rest; i++) begin
                  m_unpack_field_int[(len*32)+i] = tmp[i];
              end
          end
      end
  endfunction : m_unpack_field_int

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_field_int
//
  function logic[63:0] unpack_field_int (int size);
      if (master_packer != this)
          return master_packer.unpack_field_int(size);
      else
          return m_unpack_field_int(size);
  endfunction : unpack_field_int

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_unpack_field_element
//
  function logic[63:0] m_unpack_field_element(int size);     
      if (size != 1)
          return m_unpack_field(size);
      else begin
          if (m_bit_count == 32) begin
              if (enough_ints(1,"integral")) begin
                  count += 1;
                  m_bit_count = 0;
              end
          end
          m_unpack_field_element[0] = m_ints[count][m_bit_count];
          m_bit_count += 1;
      end
  endfunction : m_unpack_field_element

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_unpack_field
//
  function `uvm_ovm_(bitstream_t) m_unpack_field(int size);
    if (m_bit_count != 0) begin
      count += 1;
      m_bit_count = 0;
    end
    if (enough_ints(((size-1)/32)+1,"integral")) begin
      int len;
      int rest;
       
      len = size/32;  // ints
      rest = size%32; // bits
      for (int i=0; i<len; i++) begin
        m_unpack_field[(i*32)+:32] = m_ints[count];
        count += 1;
      end
      if (rest > 0) begin
        bit [31:0] tmp;
        tmp = m_ints[count];
        count += 1;
        for (int i=0; i<rest; i++) begin
          m_unpack_field[(len*32)+i] = tmp[i];
        end
      end
    end
  endfunction : m_unpack_field

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_field
//
  function `uvm_ovm_(bitstream_t) unpack_field(int size);
      if (master_packer != this)
          return master_packer.unpack_field(size);
      else
          return m_unpack_field(size);
  endfunction : unpack_field

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_field_element
//
  function logic[63:0] unpack_field_element(int size);
      if (master_packer != this)
          return master_packer.unpack_field_element(size);
      else
          return m_unpack_field_element(size);
  endfunction : unpack_field_element

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_unpack_string
//
  function string m_unpack_string(int num_chars=-1);
      bit            is_null_term; // Assumes a null terminated string
      bit [3:0][7:0] bytes;
      int        i; i = 0;

      if(num_chars == -1) is_null_term = 1;
      else is_null_term = 0;

      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      if (is_null_term==1) begin
          int j;
          while(enough_ints(1,"string")) begin
              j = 0;
              bytes = m_ints[count];
              count += 1;
              while ((j < 4) && (bytes[j] != 0)) begin
                  // because can not append byte/char to string
                  m_unpack_string = {m_unpack_string," "};
                  m_unpack_string[i] = bytes[j];
                  i += 1;
                  j += 1;
              end
              if (j < 4)
                  return m_unpack_string;
          end
      end
      else begin
          int len;
          int rest;
          len = num_chars/4;
          rest = num_chars%4;

          if (enough_ints(len,"string")) begin
              for (int j = 0; j < ((rest) ? len + 1 : len); j++) begin
                  bytes = m_ints[count];
                  count += 1;
                  for (int k = 0; k < ((j == (len -1)) ? rest : 4); k++) begin
                      // because can not append byte/char to string
                      m_unpack_string = {m_unpack_string," "};
                      m_unpack_string[i] = bytes[k];
                      i += 1;
                  end
                  j += 1;
              end
              m_unpack_string = {m_unpack_string," "};
              m_unpack_string[i] = 0;
          end
      end
  endfunction : m_unpack_string

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_string
//
  function string      unpack_string    (int num_chars=-1);
      if (master_packer != this)
          return master_packer.unpack_string(num_chars);
      else
          return m_unpack_string(num_chars);
  endfunction : unpack_string

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_time
//
  function time unpack_time();
      if (master_packer != this)
          return master_packer.unpack_time();
      else if (enough_ints(2,"time"))
          return unpack_field_int(64);
  endfunction : unpack_time

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unpack_real
//
  function real unpack_real();
      if (master_packer != this)
          return master_packer.unpack_real();
      else if (enough_ints(2,"real"))
          return $bitstoreal(unpack_field_int(64));
  endfunction : unpack_real

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::get_packed_size
//
  function int get_packed_size(); 
      if (master_packer != this)
          get_packed_size = master_packer.get_packed_size();
      else begin
          get_packed_size = m_packed_int_size;
      end
  endfunction : get_packed_size

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::get_packed_internals
//
  function `STREAM_T get_packed_internals ();
      if (master_packer != this)
          return master_packer.get_packed_internals();
      else
          return m_ints;
  endfunction : get_packed_internals

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::clear
//
  function void clear();
      reset();
      m_ints = 0;
  endfunction : clear

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_set_non_null_object
//
  function bit m_set_non_null_object(`uvm_ovm_(object) obj);
      bit ret;
      if (obj == null)
          ret = 0;
      else
          ret = 1;

      m_ints[count] = ret;
      count += 1;
      return ret;
  endfunction : m_set_non_null_object
  
// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_get_non_null_object
//
  function bit m_get_non_null_object();
      m_get_non_null_object = m_ints[count];
      count += 1;
  endfunction : m_get_non_null_object
  
// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_pack_object
//
  function void m_pack_object (`uvm_ovm_(object) obj, uvm_ml_packer_base nested_packer);
      `uvm_ovm_(void) v; v = obj;

      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      if (m_fast_object_stack.exists(obj)) begin
        `uvm_ovm_(report_warning)("CYCFND", 
                                  $psprintf("Cycle detected for object @%0d during pack", this));
         return;
      end
      if (!m_set_non_null_object(obj))
          return;

      m_fast_object_stack[v] = 1;
      uvm_object::__m_uvm_status_container.packer = nested_packer;
      nested_packer.v_marshall_object(obj);
      uvm_object::__m_uvm_status_container.packer = this;
      m_fast_object_stack.delete(v);
  endfunction : m_pack_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::set_packed_size
//
  function void set_packed_size();
      m_packed_int_size = count;
      count = 0;
      if (m_bit_count != 0) begin
          m_packed_int_size += 1;
          m_bit_count = 0;
      end
  endfunction : set_packed_size
  
// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::enough_ints
//
  function bit enough_ints(int needed, string id);
      if ((m_packed_int_size - count) < needed) begin
          `uvm_ovm_(report_error)("MLLIBPCKSZ",
                                  $psprintf("%0d ints needed to unpack %0s, yet only %0d available.",
                                   needed, id, (m_packed_int_size - count)), `UVM_OVM_(NONE));
          count -= 1; // Discard last int so that unmarshall_top_object will issue the fatal error
          return 0;
      end
      return 1;
  endfunction : enough_ints

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::reset
//
  function void reset();
      count = 0;
      m_ints = 0;
      m_bit_count = 0;
      m_packed_int_size = 0;
  endfunction : reset

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_put_packed_ints
//
  function void m_put_packed_ints (int int_size, uvm_ml_intstream_t ints);

      m_ints = ints;
      m_packed_int_size = int_size;
      count = 0;
      m_bit_count = 0;
  endfunction : m_put_packed_ints

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::unmarshall_top_object
//
  function `uvm_ovm_(object) unmarshall_top_object(int unsigned       stream_size,
                                                   uvm_ml_intstream_t stream);
      `uvm_ovm_(object) obj;

      master_packer = this;
      m_put_packed_ints(stream_size, stream);
      if (!m_get_non_null_object())
          return null;
      obj = m_type_marshall_imp.v_create_object();
      uvm_object::__m_uvm_status_container.packer = this;
      v_unmarshall_object(obj);

      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      if (m_packed_int_size != count) begin
          `uvm_ovm_(report_fatal)("UNPKSZ",
          { "Unpacked fewer ints than were packed. ", 
            " This may be due to a mismatch in class definitions across languages.",
            " Base class = ", obj.get_type_name(), "." } );
      end
      return obj;
  endfunction : unmarshall_top_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::m_unpack_object
//
  function void m_unpack_object (inout `uvm_ovm_(object) obj);
      `uvm_ovm_(object_wrapper) sv_type;
      byte                      is_non_null;
      uvm_ml_packer_base        nested_packer;
       uvm_ml_packer_base       prev_master_packer;
   
      if (m_bit_count != 0) begin
          count += 1;
          m_bit_count = 0;
      end
      if (!master_packer.m_get_non_null_object())
          return;

      obj = m_type_marshall_imp.v_create_object();
     
      nested_packer = uvm_ml_serialization_kit::get_actual_packer_for_type(obj.get_object_type());
      uvm_ml_serialization_kit::m_last_packer = nested_packer;
      prev_master_packer = nested_packer.master_packer;
      nested_packer.set_master_packer(master_packer);
      uvm_object::__m_uvm_status_container.packer = nested_packer;
      nested_packer.v_unmarshall_object(obj);

      nested_packer.set_master_packer(prev_master_packer);
      uvm_object::__m_uvm_status_container.packer = this;
  endfunction : m_unpack_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::get_packed_internals_ref
//
  function void get_packed_internals_ref (ref uvm_ml_intstream_t stream);
      stream = m_ints;
  endfunction :  get_packed_internals_ref

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_packer_base::pack_top_string
//
  function void pack_top_string(string val);
      uvm_ml_stream_kind_e kind;

      kind = UVM_ML_STREAM_STRING;

      clear();
      m_ints[0] = int'(kind);
      count += 1;
      m_pack_string(val);
      set_packed_size();
  endfunction : pack_top_string

endclass : uvm_ml_packer_base

// uvm_ml_class_packer_t
// ----------------------

class uvm_ml_class_packer_t extends uvm_ml_packer_base;

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_packer_t::new
//
  function new(); 
      super.new(); 
  endfunction : new

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_packer_t::v_marshall_object
//
  function void v_marshall_object(`uvm_ovm_(object) obj);

      m_type_marshall_imp.v_add_type_identifier(obj);
      obj.__m_uvm_field_automation(null, `UVM_OVM_(PACK),"");
      obj.do_pack(this);
  endfunction : v_marshall_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_packer_t::v_unmarshall_object
//
  function void v_unmarshall_object(inout `uvm_ovm_(object) obj);
      obj.__m_uvm_field_automation(null, `UVM_OVM_(UNPACK),"");
      obj.do_unpack(this);
  endfunction : v_unmarshall_object

endclass : uvm_ml_class_packer_t

///////////////////////

virtual class uvm_ml_class_serializer extends uvm_ml_packer_base;

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::new
//
  function new();
    super.new();
  endfunction : new
  
// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::serialize
// The user shall implement this method in the class extending
// uvm_ml_class_serializer
//
  virtual function void serialize(`uvm_ovm_(object) obj);
  endfunction : serialize

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::v_marshall_object
//
  function void v_marshall_object(`uvm_ovm_(object) obj);
      m_type_marshall_imp.v_add_type_identifier(obj);
      serialize(obj);
  endfunction : v_marshall_object

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::deserialize
// The user shall implement this method in the class extending
// uvm_ml_class_serializer
//
  virtual function void deserialize(inout `uvm_ovm_(object) obj);
      `uvm_ovm_(report_fatal) ("UVMMLNIMP", "uvm_ml_class_serializer::deserialize() id not implemented");
  endfunction : deserialize

// /////////////////////////////////////////////////////////////////
//
// uvm_ml_class_serializer::v_unmarshall_object
//
  function void v_unmarshall_object(inout `uvm_ovm_(object) obj);
    deserialize(obj);
  endfunction : v_unmarshall_object
endclass : uvm_ml_class_serializer

// Serialization API

// /////////////////////////////////////////////////////////////////
//
// register_class_serializer
//
function bit register_class_serializer (uvm_ml_class_serializer serializer, `uvm_ovm_(object_wrapper)  sv_type);
    return uvm_ml_serialization_kit::register_class_serializer (serializer, sv_type);
endfunction : register_class_serializer

// /////////////////////////////////////////////////////////////////
//
// serialize_object
//
function automatic int unsigned serialize_object(`uvm_ovm_(object) obj, ref `STREAM_T stream);
    int                int_size;
    uvm_ml_packer_base packer;

    packer = uvm_ml_serialization_kit::marshall_top_object(obj);
    packer.get_packed_internals_ref(stream);
    int_size = packer.get_packed_size();
    if (int_size > `MAX_STREAM_SIZE) begin
        string msg;
        $swrite(msg, "Packed ML UVM/OVM transaction size %d (integers) exceeded maximal stream size %d", int_size, `MAX_STREAM_SIZE);
        `uvm_ovm_(report_fatal)("XMAXSTRSZ", msg);
    end

    return int_size;
endfunction : serialize_object

// /////////////////////////////////////////////////////////////////
//
// deserialize_object
//
function automatic `uvm_ovm_(object) deserialize_object(int unsigned  stream_int_size,
                                                        ref `STREAM_T stream);
    return uvm_ml_serialization_kit::unmarshall_top_object(stream_int_size, stream);
endfunction : deserialize_object
