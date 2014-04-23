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

//-----------------------------------------------------
//
// UVM-ML configuration and resource sharing facilities
//
//-----------------------------------------------------

static bit uvm_ml_in_export_notify_resource = 0;

class m_uvm_ml_resource_notifier;
    `STREAM_T stream;
    int stream_size;

    static function uvm_ml_resource_notify_action_e resource_action_name_to_enum(string action_name);
        uvm_ml_resource_notify_action_e action_kind;

        case (action_name)
            "RESOURCE_SET": action_kind = UVM_ML_RESOURCE_SET;
            "RESOURCE_SET_DEFAULT": action_kind = UVM_ML_RESOURCE_SET;
            "RESOURCE_SET_OVERRIDE": action_kind = UVM_ML_RESOURCE_SET_OVERRIDE;
            "RESOURCE_SET_OVERRIDE_NAME": action_kind = UVM_ML_RESOURCE_SET_OVERRIDE_NAME;
            "RESOURCE_WRITE_BY_NAME": action_kind = UVM_ML_RESOURCE_WRITE_BY_NAME;
            "CONFIG_SET": action_kind = UVM_ML_CONFIG_SET;
        endcase
        return action_kind;
    endfunction : resource_action_name_to_enum

    virtual function void notify(string scope, string name, string accessor_name, string action_name, string inst_name);

        if (uvm_ml_in_export_notify_resource == 0) begin // Do not send back the notification received from the backplane
            if (action_name == "CONFIG_SET") begin
                uvm_ml_notify_config(scope, inst_name, name, stream_size, stream);
            end
            else begin
                uvm_ml_resource_notify_action_e action_kind;

                action_kind = resource_action_name_to_enum(action_name);
                uvm_ml_notify_resource(action_kind, scope, name, accessor_name, stream_size, stream);
            end
        end
    endfunction : notify
endclass : m_uvm_ml_resource_notifier

// /////////////////////////////////////////
//
// Resource integral value processing class
//
// /////////////////////////////////////////

class uvm_ml_resource_value_integral_notifier extends uvm_resource_value_integral_notifier;

  m_uvm_ml_resource_notifier m_notifier;

  function new(string name = "");
    super.new(name);
    m_notifier = new;
  endfunction : new

  `uvm_object_utils (uvm_ml_resource_value_integral_notifier)

  uvm_bitstream_t val;

  virtual function uvm_bitstream_t get_stream();
    if (m_initialized == 0)
        set_stream(val, $bits(val));
    return val; 
  endfunction : get_stream

  virtual function uvm_object get_object();
    assert (0); // Should not get here
    return null;
  endfunction : get_object

  virtual function string get_string();
    assert (0); // Should not get here
    return "";
  endfunction  : get_string

  virtual function void set_stream(uvm_bitstream_t t, int bitsize, uvm_object accessor = null);

    int kind = uvm_ml_stream_kind_e'(UVM_ML_STREAM_RAW);
    int kind2 = 'hffff;

    val = t;
    m_initialized = 1;
    
    m_notifier.stream = { val, kind};

    for (int i = $bits(val) + $bits(kind); i < $bits(m_notifier.stream); i++)
        m_notifier.stream[i] = 0;

    m_notifier.stream_size = bitsize + 32;

  endfunction : set_stream

  virtual function void set_object(uvm_object t, uvm_object accessor = null);
    assert (0); // Should not get here
  endfunction : set_object

  virtual function void set_string(string t, uvm_object accessor = null);
    assert (0); // Should not get here
  endfunction : set_string

  virtual function void notify(string scope, string name, string accessor_name, string action_name, string inst_name);

     m_notifier.notify(scope, name, accessor_name, action_name, inst_name);
  endfunction : notify
endclass : uvm_ml_resource_value_integral_notifier

// ///////////////////////////////////////////
//
// Resource uvm_object value processing class
//
// ///////////////////////////////////////////

class uvm_ml_resource_value_object_notifier extends uvm_resource_value_object_notifier;

  m_uvm_ml_resource_notifier m_notifier;

  function new(string name = "");
    super.new(name);
    m_notifier = new;
  endfunction : new

  `uvm_object_utils (uvm_ml_resource_value_object_notifier)

  uvm_object val;

  virtual function uvm_bitstream_t get_stream();
    assert (0); // Should not get here
    return 0;
  endfunction : get_stream

  virtual function uvm_object get_object();
    if (m_initialized == 0)
      set_object(val);
    return val;
  endfunction : get_object

  virtual function string get_string();
    assert (0); // Should not get here
    return "";
  endfunction : get_string

  virtual function void set_stream(uvm_bitstream_t t, int bitsize, uvm_object accessor = null);
    assert (0); // Should not get here
  endfunction : set_stream

  virtual function void set_object(uvm_object t, uvm_object accessor = null);

    m_initialized = 1;
    val = t;
    m_notifier.stream_size = uvm_ml_serialization_kit::pack_cur_stream(val, m_notifier.stream);
  endfunction : set_object

  virtual function void set_string(string t, uvm_object accessor = null);
    assert (0); // Should not get here
  endfunction : set_string

  virtual function void notify(string scope, string name, string accessor_name, string action_name, string inst_name);
     m_notifier.notify(scope, name, accessor_name, action_name, inst_name);
  endfunction
endclass : uvm_ml_resource_value_object_notifier

// /////////////////////////////////////////
//
// Resource string value processing class
//
// /////////////////////////////////////////

class uvm_ml_resource_value_string_notifier extends uvm_resource_value_string_notifier;

  m_uvm_ml_resource_notifier m_notifier;

  function new(string name = "");
    super.new(name);
    m_notifier = new;
  endfunction : new

  `uvm_object_utils (uvm_ml_resource_value_string_notifier)

  string val;

  virtual function uvm_bitstream_t get_stream();
    assert (0); // Should not get here
    return 0;
  endfunction : get_stream

  virtual function uvm_object get_object();
    assert (0); // Should not get here
    return null;
  endfunction : get_object

  virtual function string get_string();
    if (m_initialized == 0)
        set_string(val);
    return val;
  endfunction : get_string

  virtual function void set_stream(uvm_bitstream_t t, int bitsize, uvm_object accessor = null);
    assert (0); // Should not get here
  endfunction : set_stream

  virtual function void set_object(uvm_object t, uvm_object accessor = null);
    assert (0); // Should not get here
  endfunction : set_object

  virtual function void set_string(string t, uvm_object accessor = null);
    m_initialized = 1;
    val = t;

    m_notifier.stream_size = uvm_ml_serialization_kit::pack_top_string(val, m_notifier.stream);
  endfunction : set_string

  virtual function void notify(string scope, string name, string accessor_name, string action_name, string inst_name);
    m_notifier.notify(scope, name, accessor_name, action_name, inst_name);
  endfunction : notify

endclass : uvm_ml_resource_value_string_notifier

typedef class uvm_ml_resource_db_caller;

typedef class uvm_ml_resource_db_set_caller;
typedef class uvm_ml_resource_db_set_default_caller;
typedef class uvm_ml_resource_db_set_override_caller;
typedef class uvm_ml_resource_db_set_override_name_caller;
typedef class uvm_ml_resource_db_write_by_name_caller;
typedef class uvm_ml_resource_db_config_set_caller;

// /////////////////////////////////////////////////
//
// Virtual base clss uvm_ml_resource_db_caller #(T, CONFIG_DB_T)
//
// /////////////////////////////////////////////////
  
virtual class uvm_ml_resource_db_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T));

    static uvm_ml_resource_db_caller#(T, CONFIG_DB_T)  m_resource_db_callers[uvm_ml_resource_notify_action_e];

    static bit initialized;

    extern static function void initialize();

    static function uvm_ml_resource_db_caller#(T, CONFIG_DB_T) get_caller(uvm_ml_resource_notify_action_e action);
        if (!initialized) initialize();
        return m_resource_db_callers[action];
    endfunction

    pure virtual function bit call_db(string       scope,
                                      string       name,
                                      T            val,
                                      string       accessor_name);
endclass : uvm_ml_resource_db_caller

// ///////////////////////////////////
//
// uvm_ml_resource_db_set_caller #(T)
//
// ///////////////////////////////////
  
class uvm_ml_resource_db_set_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T)) extends uvm_ml_resource_db_caller #(T, CONFIG_DB_T);

    typedef uvm_ml_resource_db_set_caller #(T, CONFIG_DB_T) this_type;

    static this_type m_caller;

    static function uvm_ml_resource_db_caller #(T, CONFIG_DB_T) get();
        if (m_caller == null)
            m_caller = new;
        return m_caller;
    endfunction

    virtual function bit call_db(string       scope,
                                 string       name,
                                 T            val,
                                 string       accessor_name);
        uvm_resource_db#(T)::set(scope, name, val, null);
        return 1;
    endfunction   
endclass : uvm_ml_resource_db_set_caller

// ///////////////////////////////////////////
//
// uvm_ml_resource_db_set_default_caller #(T)
//
// ///////////////////////////////////////////
  
class uvm_ml_resource_db_set_default_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T)) extends uvm_ml_resource_db_caller #(T, CONFIG_DB_T);

    typedef uvm_ml_resource_db_set_default_caller #(T, CONFIG_DB_T) this_type;

    static this_type m_caller;

    static function uvm_ml_resource_db_caller #(T, CONFIG_DB_T) get();
        if (m_caller == null)
            m_caller = new;
        return m_caller;
    endfunction

    virtual function bit call_db(string       scope,
                                 string       name,
                                 T            val,
                                 string       accessor_name);
        void'(uvm_resource_db#(T)::set_default(scope, name));
        return 1;
    endfunction  
endclass : uvm_ml_resource_db_set_default_caller

// ////////////////////////////////////////////
//
// uvm_ml_resource_db_set_override_caller #(T)
//
// ////////////////////////////////////////////
  
class uvm_ml_resource_db_set_override_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T)) extends uvm_ml_resource_db_caller #(T, CONFIG_DB_T);

    typedef uvm_ml_resource_db_set_override_caller #(T, CONFIG_DB_T) this_type;

    static this_type m_caller;

    static function uvm_ml_resource_db_caller #(T, CONFIG_DB_T) get();
        if (m_caller == null)
            m_caller = new;
        return m_caller;
    endfunction

    virtual function bit call_db(string       scope,
                                 string       name,
                                 T            val,
                                 string       accessor_name);
        uvm_resource_db#(T)::set_override(scope, name, val, null);
        return 1;
    endfunction   
endclass : uvm_ml_resource_db_set_override_caller

// /////////////////////////////////////////////////
//
// uvm_ml_resource_db_set_override_name_caller #(T, CONFIG_DB_T)
//
// /////////////////////////////////////////////////
  
class uvm_ml_resource_db_set_override_name_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T)) extends uvm_ml_resource_db_caller #(T, CONFIG_DB_T);

    typedef uvm_ml_resource_db_set_override_name_caller #(T, CONFIG_DB_T) this_type;

    static this_type m_caller;

    static function uvm_ml_resource_db_caller #(T, CONFIG_DB_T) get();
        if (m_caller == null)
            m_caller = new;
        return m_caller;
    endfunction

    virtual function bit call_db(string       scope,
                                 string       name,
                                 T            val,
                                 string       accessor_name);
        uvm_resource_db#(T)::set_override_name(scope, name, val, null);
        return 1;
    endfunction
endclass : uvm_ml_resource_db_set_override_name_caller

// /////////////////////////////////////////////
//
// uvm_ml_resource_db_write_by_name_caller #(T, CONFIG_DB_T)
//
// /////////////////////////////////////////////
  
class uvm_ml_resource_db_write_by_name_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T)) extends uvm_ml_resource_db_caller #(T, CONFIG_DB_T);

    typedef uvm_ml_resource_db_write_by_name_caller #(T, CONFIG_DB_T) this_type;

    static this_type m_caller;

    static function uvm_ml_resource_db_caller #(T, CONFIG_DB_T) get();
        if (m_caller == null)
            m_caller = new;
        return m_caller;
    endfunction

    virtual function bit call_db(string       scope,
                                 string       name,
                                 T            val,
                                 string       accessor_name);
        return uvm_resource_db#(T)::write_by_name(scope, name, val, null);
    endfunction
endclass : uvm_ml_resource_db_write_by_name_caller

// ///////////////////////////////////////////
//
// uvm_ml_resource_db_config_set_caller #(T, CONFIG_DB_T)
//
// ///////////////////////////////////////////
  
class uvm_ml_resource_db_config_set_caller #(type T = uvm_bitstream_t, type CONFIG_DB_T = uvm_config_db#(T)) extends uvm_ml_resource_db_caller #(T, CONFIG_DB_T);

    typedef uvm_ml_resource_db_config_set_caller #(T, CONFIG_DB_T) this_type;

    static this_type m_caller;

    static function uvm_ml_resource_db_caller #(T, CONFIG_DB_T) get();
        if (m_caller == null)
            m_caller = new;
        return m_caller;
    endfunction

    virtual function bit call_db(string       scope,
                                 string       name,
                                 T            val,
                                 string       accessor_name);
        int depth;

        depth = 1;
        foreach(accessor_name[i])
            if (accessor_name[i] == ".") ++depth;

        // We rely on export_notify_config() that scope was already concatenated from cntxt and instance_name

        CONFIG_DB_T::set_by_cntxt_name("", scope, name, val, depth);
        return 1;
    endfunction
endclass : uvm_ml_resource_db_config_set_caller

function void uvm_ml_resource_db_caller::initialize();

    m_resource_db_callers[UVM_ML_RESOURCE_SET] = uvm_ml_resource_db_set_caller#(T, CONFIG_DB_T)::get();
    m_resource_db_callers[UVM_ML_RESOURCE_SET_DEFAULT] = uvm_ml_resource_db_set_default_caller#(T, CONFIG_DB_T)::get();
    m_resource_db_callers[UVM_ML_RESOURCE_SET_OVERRIDE] = uvm_ml_resource_db_set_override_caller#(T, CONFIG_DB_T)::get();
    m_resource_db_callers[UVM_ML_RESOURCE_SET_OVERRIDE_NAME] = uvm_ml_resource_db_set_override_name_caller#(T, CONFIG_DB_T)::get();
    m_resource_db_callers[UVM_ML_RESOURCE_WRITE_BY_NAME] = uvm_ml_resource_db_write_by_name_caller#(T, CONFIG_DB_T)::get();
    m_resource_db_callers[UVM_ML_CONFIG_SET] = uvm_ml_resource_db_config_set_caller#(T, CONFIG_DB_T)::get();

    initialized = 1;
endfunction

function bit uvm_ml_set_resource(uvm_ml_resource_notify_action_e action,
                                 string                          scope,
                                 string                          name,
                                 string                          accessor_name,
                                 int unsigned                    stream_size,
                                 `STREAM_T                       stream);
    bit                  result;
    uvm_ml_stream_kind_e kind;

    uvm_ml_in_export_notify_resource = 1;

    kind = uvm_ml_stream_kind_e'(stream[0]);

    if (kind == UVM_ML_STREAM_STRING) begin
        string                             val;
        uvm_ml_resource_db_caller#(string, uvm_extended_string_config_db) caller_object;

        val = uvm_ml_serialization_kit::unpack_top_string(stream_size, stream);

        caller_object = uvm_ml_resource_db_caller#(string,uvm_extended_string_config_db)::get_caller(action);
        result = caller_object.call_db(scope, name, val, accessor_name);
    end
    else if (kind == UVM_ML_STREAM_RAW) begin
        uvm_bitstream_t     val;
        uvm_ml_resource_db_caller#(uvm_bitstream_t, uvm_extended_singular_config_db#(uvm_bitstream_t)) caller_object;

        assert (stream_size > $bits(kind)); // Else internal error

        {val, kind} = stream; 

        for (int i = stream_size - $bits(kind); i < $bits(val); i++)
            val[i] = 0;

        caller_object = uvm_ml_resource_db_caller#(uvm_bitstream_t, uvm_extended_singular_config_db#(uvm_bitstream_t))::get_caller(action);
        result = caller_object.call_db(scope, name, val, accessor_name); // This is temporary quick solution -
                                                                         // retrieval will work only via
                                                                         // uvm_resource_db#(uvm_bitstream_t)
                                                                         // and not - via uvm_resource_db#(actual_type).
                                                                         // Later we can add an intermediate pool and
                                                                         // override the resources pool so it will
                                                                         // search in the intermediate pool first
    end
    else begin // kind == UVM_ML_STREAM_TYPED_OBJECT or null
        int unsigned stream_int_size;
        stream_int_size = stream_size/32;
        if (uvm_ml_serialization_kit::is_registered_object_type(stream_int_size, stream)) begin // STREAMSIZE: is_registered_object_type() receives size in ints
            uvm_object                             val;
            uvm_ml_resource_db_caller#(uvm_object, uvm_extended_singular_config_db#(uvm_object)) caller_object;

            val = uvm_ml_serialization_kit::unmarshall_top_object(stream_int_size, stream); // STREAMSIZE: unmarshall_top_object receives size in ints

            caller_object = uvm_ml_resource_db_caller#(uvm_object, uvm_extended_singular_config_db#(uvm_object))::get_caller(action);
            result = caller_object.call_db(scope, name, val, accessor_name);
        end
        else begin
            // The incoming stream is typed on the initiator side but does not match any uvm_object
            // on the UVM SV side. It may be not targeted to SV (broadcasted by the backplane) or
            // intended to be mapped to a non-uvm_object type, for example, to a SV struct. 
            // In order to support the latter, we deserialize the stream to a raw stream and keep
            // the configuration element
            
            uvm_bitstream_t                             val;
            int                                         type_id;
            uvm_ml_resource_db_caller#(uvm_bitstream_t, uvm_extended_singular_config_db#(uvm_bitstream_t)) caller_object;

            assert ((stream_size) > $bits(kind)); // STREAMSIZE: Switching to bit size on the Backplane APi level
                                                  // Else internal error
            {val, type_id, kind} = stream;
            for (int i = (stream_size) - $bits(kind); i < $bits(val); i++) // STREAMSIZE
                val[i] = 0;
            caller_object = uvm_ml_resource_db_caller#(uvm_bitstream_t, uvm_extended_singular_config_db#(uvm_bitstream_t))::get_caller(action);
            result = caller_object.call_db(scope, name, val, accessor_name);        
        end
    end
    uvm_ml_in_export_notify_resource = 0;
    return result;
endfunction : uvm_ml_set_resource

