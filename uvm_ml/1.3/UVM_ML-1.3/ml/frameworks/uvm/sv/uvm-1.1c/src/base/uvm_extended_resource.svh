//----------------------------------------------------------------------
//   Copyright 2011 Cypress Semiconductor
//   Copyright 2010 Mentor Graphics Corporation
//   Copyright 2011 Cadence Design Systems, Inc. 
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

//----------------------
// ML Additions (START)
//----------------------
//----------------------------------------------------------------------
// Class: uvm_resource_value_notifier_base
//
//----------------------------------------------------------------------

virtual class uvm_resource_value_notifier_base extends uvm_object;
  function new(string name = "");
    super.new(name);
  endfunction

  bit m_initialized;

  virtual function uvm_bitstream_t get_stream();
    uvm_report_error("RSRCGETSTREAM", 
        "function uvm_resource_value_notifier_base::get_stream() not implemented");
    return 0; 
  endfunction

  virtual function uvm_object get_object();
    uvm_report_error("RSRCGETOBJ", 
        "function uvm_resource_value_notifier_base::get_object() not implemented");
    return null; 
  endfunction

  virtual function string get_string();
    uvm_report_error("RSRCGETSTRING", 
        "function uvm_resource_value_notifier_base::get_string() not implemented");
    return ""; 
  endfunction

  virtual function void set_stream(uvm_bitstream_t t, int bitsize, uvm_object accessor = null);
    uvm_report_error("RSRCSETSTREAM", "function uvm_resource_value_notifier_base::set_stream() not implemented");
  endfunction

  virtual function void set_object(uvm_object t, uvm_object accessor = null);
    uvm_report_error("RSRCSETOBJ", "function uvm_resource_value_notifier_base::set_object() not implemented");
  endfunction

  virtual function void set_string(string t, uvm_object accessor = null);
    uvm_report_error("RSRCSETSTR", "function uvm_resource_value_notifier_base::set_string() not implemented");
  endfunction

  virtual function void notify(string scope, string name, string accessor_name, string action_name, string inst_name);
    uvm_report_error("RSRCNOTIFY", "function uvm_resource_value_notifier_base::notify() not implemented");
  endfunction

endclass : uvm_resource_value_notifier_base

`define uvm_object_utils_no_registered_converter_begin(T) \
   `m_uvm_object_registry_internal(T,T)  \
   `m_uvm_object_create_func(T) \
   `m_uvm_get_type_name_func(T) \
   `uvm_field_utils_begin(T) 

//----------------------------------------------------------------------
// Class: uvm_resource_value_integral_notifier
//
// The predefined defintion of this class is empty but it can be overriden
// by a user in order to implement a notification callback.
// In such case the user implementation shall implement methods set_stream() and get_stream()
//----------------------------------------------------------------------

class uvm_resource_value_integral_notifier extends uvm_resource_value_notifier_base;

  `uvm_object_utils_no_registered_converter_begin(uvm_resource_value_integral_notifier)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction
endclass : uvm_resource_value_integral_notifier

//----------------------------------------------------------------------
// Class: uvm_resource_value_object_notifier
//
// The predefined defintion of this class is empty but it can be overriden
// by a user in order to implement a notification callback.
// In such case the user implementation shall implement methods set_object() and get_object()
//----------------------------------------------------------------------

class uvm_resource_value_object_notifier extends uvm_resource_value_notifier_base;

  function new(string name = "");
    super.new(name);
  endfunction

  `uvm_object_utils_no_registered_converter_begin(uvm_resource_value_object_notifier)
  `uvm_object_utils_end

endclass : uvm_resource_value_object_notifier

//----------------------------------------------------------------------
// Class: uvm_resource_value_string_notifier
//
// The predefined defintion of this class is empty but it can be overriden
// by a user in order to implement a notification callback.
// In such case the user implementation shall implement methods set_string() and get_string()
//----------------------------------------------------------------------

class uvm_resource_value_string_notifier extends uvm_resource_value_notifier_base;

  function new(string name = "");
    super.new(name);
  endfunction

  `uvm_object_utils_no_registered_converter_begin(uvm_resource_value_string_notifier)
  `uvm_object_utils_end
endclass : uvm_resource_value_string_notifier

//----------------------------------------------------------------------
// Class: uvm_resource_value_default_notifier
//
// Implements a default mechanism for strorage and retrieval of the resource
// value if it does not need or cannot be transmitted to a callback
//----------------------------------------------------------------------

class uvm_resource_value_default_notifier #(type T=int);

  typedef uvm_resource_value_default_notifier#(T) this_type;

  T val;

  function T read();
    return val;
  endfunction

  function void write(T t);
    val = t;
  endfunction

endclass : uvm_resource_value_default_notifier

typedef class uvm_resource; // forward reference
typedef class uvm_extended_singular_resource;

//----------------------------------------------------------------------
// Class: uvm_resource_value_holder_base;
//
// Base class implementation of a resource value holder object
//----------------------------------------------------------------------

virtual class uvm_resource_value_holder_base;

  uvm_resource_value_notifier_base value_notifier;

  uvm_resource_base this_resource_kind_type_handle;

  extern static function uvm_resource_base get_resource_of_bitstream_t_type();

  extern static function uvm_resource_base get_resource_of_uvm_object_type();

  extern static function uvm_resource_base get_resource_of_string_type();

  // Static variables are used at runtime to identify the resource value kind: 
  // integral, object, string or none of them
  static uvm_resource_base integral_resource_type_handle = get_resource_of_bitstream_t_type();

  static uvm_resource_base object_resource_type_handle = get_resource_of_uvm_object_type();

  static uvm_resource_base string_resource_type_handle = get_resource_of_string_type();

  function void notify(string scope, string name, string accessor_name, string action_name, string inst_name);
    if (value_notifier != null)
        value_notifier.notify (scope, name, accessor_name, action_name, inst_name);
  endfunction

  function void copy_from_compatible_base(uvm_resource_value_holder_base base_holder);

    this_resource_kind_type_handle = base_holder.this_resource_kind_type_handle; // Must assign
                                                                                 // because kind_type_handle of
                                                                                 // objects in null upon
                                                                                 // construction
    value_notifier = base_holder.value_notifier;
    
  endfunction : copy_from_compatible_base

endclass : uvm_resource_value_holder_base

//----------------------------------------------------------------------
// Class: uvm_resource_value_holder #(T)
//
// Parameterized resource value holder
//----------------------------------------------------------------------

class uvm_resource_value_holder #(type T=int) extends uvm_resource_value_holder_base;

  typedef uvm_resource_value_holder#(T) this_type;

  uvm_resource_value_default_notifier #(T) default_notifier;

  function new();

    T t;

    if (uvm_resource_options::is_notifying()) begin
      string tmp_string;
      if ($typename(T) == "string" 
`ifndef QUESTA
        && ($cast(tmp_string, t) == 1)
`endif
      ) begin
        value_notifier = uvm_resource_value_string_notifier::type_id::create("value_notifier");
        this_resource_kind_type_handle = string_resource_type_handle;
      end
      else begin
        uvm_bitstream_t tmp;
        if ($cast(tmp, t) == 1) begin
          value_notifier = uvm_resource_value_integral_notifier::type_id::create("value_notifier");
          this_resource_kind_type_handle = integral_resource_type_handle;
        end
        // We cannot deduct whether a type is a uvm_object at this point without an actual value
      end
    end
    else    
      default_notifier = new;
  endfunction

  function T read();

    T res;

    if (default_notifier != null)
      res = default_notifier.read();
    else begin
      if (this_resource_kind_type_handle == integral_resource_type_handle)
        $cast(res, value_notifier.get_stream());
      else if (this_resource_kind_type_handle == object_resource_type_handle)
        $cast(res, value_notifier.get_object());
`ifndef QUESTA
      else if (this_resource_kind_type_handle == string_resource_type_handle)
        $cast(res, value_notifier.get_string());
`endif
      // else means read() was called before write - so simply return the initial type value in res
    end
    return res;
  endfunction

  function void write(uvm_resource_base rsrc, T t, uvm_object accessor = null);

    if ((default_notifier == null) && (this_resource_kind_type_handle == null)) begin
      // Check whether T is a uvm_object
      uvm_object tmp_object;

      if ($cast(tmp_object, t) == 1) begin
        this_resource_kind_type_handle = object_resource_type_handle;
        value_notifier = uvm_resource_value_object_notifier::type_id::create("value_notifier");
      end
      else
        default_notifier = new;
    end

    if (default_notifier != null)
      default_notifier.write(t);
    else begin
      if (this_resource_kind_type_handle == integral_resource_type_handle) begin
        uvm_bitstream_t tmp;
        // Unfortunately this does not pass elaboration: int s = $bits(T);
        int s = $bits(tmp);

        $cast(tmp, t);
        value_notifier.set_stream(tmp, s, accessor);
      end
      else if (this_resource_kind_type_handle == object_resource_type_handle) begin
        uvm_object tmp_object;
        $cast(tmp_object, t);
        value_notifier.set_object(tmp_object, accessor);
      end
`ifndef QUESTA
      else if (this_resource_kind_type_handle == string_resource_type_handle) begin
        string tmp_string;
        $cast(tmp_string, t);
        value_notifier.set_string(tmp_string, accessor);
      end
`endif
      // TBD Else add an internal error
    end
  endfunction

  static function uvm_resource_value_holder_base is_base_convertible(uvm_resource_base rsrc_base);

    T                              val;
    uvm_resource_base              rsrc_base_type_handle;
    uvm_resource_value_holder_base ret;

    rsrc_base_type_handle = rsrc_base.get_type_handle();
    if (rsrc_base_type_handle == integral_resource_type_handle) begin
      uvm_bitstream_t tmp_stream;

      if ($cast(val, tmp_stream)) begin
        uvm_extended_singular_resource#(uvm_bitstream_t) stream_rsrc;

        $cast(stream_rsrc, rsrc_base);
        ret = stream_rsrc.value_holder;
      end
    end
    else if (rsrc_base_type_handle == object_resource_type_handle) begin
      uvm_extended_singular_resource#(uvm_object) object_rsrc;
      uvm_object                base_val;

      $cast(object_rsrc, rsrc_base);
      assert (object_rsrc != null);

      base_val = object_rsrc.value_holder.read();
      if ($cast(val, base_val)) begin
        ret = object_rsrc.value_holder;
      end
    end // Note that string type should provide an exact match and hence is_base_convertible should not be called

    return ret;
  endfunction : is_base_convertible

  function void copy_from_compatible_base(uvm_resource_value_holder_base base_holder);
    assert (default_notifier == null); // it should not get there with a default notifier

    this_resource_kind_type_handle = base_holder.this_resource_kind_type_handle; // Must assign
                                                                                 // because kind_type_handle of
                                                                                 // objects in null upon
                                                                                 // construction
    value_notifier = base_holder.value_notifier;
    
  endfunction : copy_from_compatible_base

endclass : uvm_resource_value_holder

class uvm_extended_singular_resource #(type T=int) extends uvm_resource #(T);

  typedef uvm_resource#(T) this_type_base;
  typedef uvm_extended_singular_resource#(T) this_type_actual;

  // Can't be rand since things like rand strings are not legal.
  // protected T val;
  uvm_resource_value_holder #(T) value_holder;

  function new(string name="", scope="");
    super.new(name, scope);

    value_holder = new;
  endfunction

  virtual
  function string convert2string();
    void'(m_get_converter());

//    return m_r2s.convert2string(val);
    return m_r2s.convert2string(value_holder.read());
  endfunction

  static function this_type_base get_by_name_compatible (string scope,
                                                         string name,
                                                         bit rpterr = 1);
    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    this_type_base    rsrc;

    rsrc_base = rp.get_by_name(scope, name, null, 0); // Find a resource of any type bearing this name
    if (rsrc_base == null) 
      return null;

    if (get_type() == rsrc_base.get_type_handle()) // exact match
      $cast(rsrc, rsrc_base);
    else if (is_base_convertible(rsrc_base, rsrc)) begin
      if (rsrc != null)
        rsrc.set_override();
      else begin
        string msg;
        rsrc = null;
        if(rpterr) begin
          $sformat(msg, "Resource with name %s in scope %s in the resource database exists but has incompatible value type", name, scope);
          `uvm_warning("RSRCTYPEINC", msg);
        end
      end
    end
    return rsrc;
  endfunction

  static function this_type_base get_by_name(string scope,
                                             string name,
                                             bit rpterr = 1);

    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    this_type_base rsrc;
    string msg;

//----------------------
// ML Additions (START)
//----------------------
    if (uvm_resource_options::is_notifying())
      return get_by_name_compatible (scope, name, rpterr);
//--------------------
// ML Additions (END)
//--------------------

    rsrc_base = rp.get_by_name(scope, name, my_type, rpterr);
    if(rsrc_base == null)
      return null;

    if(!$cast(rsrc, rsrc_base)) begin
      if(rpterr) begin
        $sformat(msg, "Resource with name %s in scope %s has incorrect type", name, scope);
        `uvm_warning("RSRCTYPE", msg);
      end
      return null;
    end

    return rsrc;
    
  endfunction

  virtual
  function T read(uvm_object accessor = null);
    record_read_access(accessor);
//----------------------
// ML Additions (START)
//----------------------

//    return val;
    return value_holder.read();
//--------------------
// ML Additions (END)
//--------------------
  endfunction

  virtual
  function void write(T t, uvm_object accessor = null);

    if(is_read_only()) begin
      uvm_report_error("resource", $sformatf("resource %s is read only -- cannot modify", get_name()));
      return;
    end

    // Set the modified bit and record the transaction only if the value
    // has actually changed.

//----------------------
// ML Additions (START)
//----------------------
//    if(val == t)

    if (value_holder.read() == t)
//--------------------
// ML Additions (END)
//--------------------
      return;

    record_write_access(accessor);

    // set the value and set the dirty bit
//----------------------
// ML Additions (START)
//----------------------
//    val = t;
    value_holder.write(this, t, accessor);
//--------------------
// ML Additions (END)
//--------------------
    modified = 1;
  endfunction

//----------------------
// ML Additions (START)
//----------------------

  virtual function void notify(string scope, string name, uvm_object accessor, string action_name, string inst_name = "");
    string accessor_name;

    if (accessor != null) accessor_name = accessor.get_full_name();

    value_holder.notify(scope, name, accessor_name, action_name, inst_name);
  endfunction : notify

  static function this_type_actual refine(uvm_resource_base rsrc_base, uvm_resource_value_holder_base base_holder);
    this_type_actual result;

    result = new (rsrc_base.get_name(), rsrc_base.get_scope());

    if (rsrc_base.is_read_only())
      result.set_read_only();
    else
      result.set_read_write();
    result.precedence = rsrc_base.precedence;
    result.m_is_regex_name = rsrc_base.m_is_regex_name;

    result.value_holder.copy_from_compatible_base(base_holder);
    return result;
  endfunction : refine

  static function bit is_base_convertible(uvm_resource_base rsrc_base, output this_type_actual rsrc);
    uvm_resource_value_holder_base holder;

    holder = uvm_resource_value_holder#(T)::is_base_convertible(rsrc_base);
    if (holder == null)
      return 0;
    else begin
      rsrc = refine(rsrc_base, holder);
      return 1;
    end
  endfunction : is_base_convertible

endclass : uvm_extended_singular_resource

function uvm_resource_base uvm_resource_value_holder_base::get_resource_of_bitstream_t_type();
  return uvm_resource#(uvm_bitstream_t)::get_type();
endfunction

function uvm_resource_base uvm_resource_value_holder_base::get_resource_of_uvm_object_type();
  return uvm_resource#(uvm_object)::get_type();
endfunction

function uvm_resource_base uvm_resource_value_holder_base::get_resource_of_string_type();
  return uvm_resource#(string)::get_type();
endfunction

// ----------

typedef class uvm_config_object_wrapper;

class uvm_extended_singular_config_db#(type T=int) extends uvm_config_db#(T);

  static uvm_extended_singular_config_db#(T) imp;
  static uvm_config_db#(T)          old_imp;

  virtual function uvm_resource#(T) m_new_resource(string field_name,
                                                   string inst_name);
    uvm_extended_singular_resource#(T) result;

    result = new(field_name, inst_name);

    return result;
  endfunction

  virtual function bit m_is_resource_base_convertible(uvm_resource_base rsrc_base, uvm_resource#(T) r);
    return uvm_extended_singular_resource#(T)::is_base_convertible(rsrc_base, r);
  endfunction

  virtual function bit m_get_compatible_value(uvm_component cntxt,
                                              string        inst_name,
                                              string        field_name,
                                              inout T       value,
                                              output bit    found);

    uvm_resource_pool            rp = uvm_resource_pool::get();
    uvm_resource_base            rsrc_base;
    uvm_resource_types::rsrc_q_t rq;
    uvm_extended_singular_resource#(T)    r;

    if (uvm_resource_options::is_notifying() == 0)
      return 0;

    rq = rp.lookup_regex_names(inst_name, field_name, null);

    rsrc_base = rp.get_highest_precedence(rq);
    if (rsrc_base == null) begin
      found = 0;
      return 1;
    end
    else if ($cast(r, rsrc_base) == 0) begin // not the extended_singular_resource of the given type
      if (rsrc_base.get_type_handle() == 
                 uvm_extended_singular_resource#(uvm_config_object_wrapper)::get_type()) begin
        uvm_resource#(uvm_config_object_wrapper) rcow;
        uvm_config_object_wrapper                cow;

        $cast(rcow, rsrc_base);
        cow = rcow.read();

        if ($cast(value, cow.obj)) begin
          found = 1;
          return 1;
        end
        else begin
          found = 0;
          return 1;           
        end
      end else begin
        if (uvm_extended_singular_resource#(T)::is_base_convertible(rsrc_base, r)) begin
          if (r != null) begin
            r.set_override();
          end
        end
        else begin
          found = 0;
          return 1;
        end
      end
    end

    if(uvm_config_db_options::is_tracing())
      m_show_msg("CFGDB/GET", "Configuration","read", inst_name, field_name, cntxt, r);

    if (r == null) begin
      found = 0;
      return 1;
    end
    value = r.read(cntxt);
    found = 1;
    return 1;
  endfunction

  virtual function uvm_resource#(T) m_get_by_name(string inst_name,
                                                  string field_name,
                                                  bit    rpterr=1);
    return uvm_extended_singular_resource#(T)::get_by_name(inst_name,field_name,rpterr);
  endfunction

  virtual function void m_notify(uvm_resource#(T) rsrc, 
                                 string           cntxt_name, 
                                 string           field_name, 
                                 uvm_object       accessor, 
                                 string           action_name, 
                                 string           inst_name);

    uvm_extended_singular_resource #(T) r;

    assert ($cast(r, rsrc) == 1);

    if (uvm_resource_options::is_notifying())
        r.notify(cntxt_name, field_name, accessor, action_name, inst_name);
  endfunction

  static function bit get(uvm_component cntxt,
                          string inst_name,
                          string field_name,
                          inout T value);
    bit result;
    uvm_config_db#(T) sav_imp;

    if (imp == null)
      imp = new;

    sav_imp = uvm_config_db#(T)::change_implementation(imp);

    result = uvm_config_db#(T)::get(cntxt, inst_name, field_name, value);

    uvm_config_db#(T)::restore_implementation(sav_imp);

    // Every time return implementation to be the generic one so that the direct access via uvm_config_db::get()
    // will behave consistently - before or after uvm_extended_singular_config_db::get()
    return result;
  endfunction

  static function void set(uvm_component cntxt,
                           string inst_name,
                           string field_name,
                           T value);

    uvm_config_db#(T) sav_imp;

    if (imp == null)
      imp = new;
    sav_imp = uvm_config_db#(T)::change_implementation(imp);

    uvm_config_db#(T)::set(cntxt, inst_name, field_name, value);
    uvm_config_db#(T)::restore_implementation(sav_imp);

  endfunction

  static function void set_by_cntxt_name(string        cntxt_name,
                                         string        inst_name,
                                         string        field_name,
                                         T             value,
                                         int           cntxt_depth,
                                         uvm_component accessor = null);
    uvm_config_db#(T) sav_imp;
    if (imp == null)
      imp = new;

    sav_imp = uvm_config_db#(T)::change_implementation(imp);
    do_set(cntxt_name, inst_name, field_name, value, cntxt_depth, accessor);
    uvm_config_db#(T)::restore_implementation(sav_imp);
  endfunction
endclass

// --------------------------

// Temporary implementation till some simulators do not support $cast for strings

class uvm_extended_string_resource_value_holder extends uvm_resource_value_holder_base;

  uvm_resource_value_default_notifier #(string) default_notifier;

  function new();

    string t;

    if (uvm_resource_options::is_notifying()) begin
      value_notifier = uvm_resource_value_string_notifier::type_id::create("value_notifier");
      this_resource_kind_type_handle = string_resource_type_handle;
    end
    else    
      default_notifier = new;
  endfunction

  function string read();

    string res;

    if (default_notifier != null)
      res = default_notifier.read();
    else
      res = value_notifier.get_string();

    return res;
  endfunction

  function void write(uvm_resource_base rsrc, string t, uvm_object accessor = null);

    if (default_notifier != null)
      default_notifier.write(t);
    else
      value_notifier.set_string(t, accessor);
  endfunction

endclass : uvm_extended_string_resource_value_holder


class uvm_extended_string_resource extends uvm_resource #(string);

  typedef uvm_resource#(string) this_type_base;

  // Can't be rand since things like rand strings are not legal.
  uvm_extended_string_resource_value_holder value_holder;

  function new(string name="", scope="");
    super.new(name, scope);

    value_holder = new;
  endfunction

  virtual
  function string convert2string();
    void'(m_get_converter());

//    return m_r2s.convert2string(val);
    return m_r2s.convert2string(value_holder.read());
  endfunction

  static function this_type_base get_by_name_compatible (string scope,
                                                         string name,
                                                         bit rpterr = 1);
    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    this_type_base    rsrc;

    rsrc_base = rp.get_by_name(scope, name, null, 0); // Find a resource of any type bearing this name
    if (rsrc_base == null) 
      return null;

    if (get_type() == rsrc_base.get_type_handle()) // for strings - exact match only
      $cast(rsrc, rsrc_base);

    return rsrc;
  endfunction

  static function this_type_base get_by_name(string scope,
                                             string name,
                                             bit rpterr = 1);

    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_base rsrc_base;
    this_type_base rsrc;
    string msg;

    if (uvm_resource_options::is_notifying())
      return get_by_name_compatible (scope, name, rpterr);

    rsrc_base = rp.get_by_name(scope, name, my_type, rpterr);
    if(rsrc_base == null)
      return null;

    if(!$cast(rsrc, rsrc_base)) begin
      if(rpterr) begin
        $sformat(msg, "Resource with name %s in scope %s has incorrect type", name, scope);
        `uvm_warning("RSRCTYPE", msg);
      end
      return null;
    end

    return rsrc;    
  endfunction

  virtual
  function string read(uvm_object accessor = null);
    record_read_access(accessor);
    return value_holder.read();
  endfunction

  virtual
  function void write(string t, uvm_object accessor = null);

    if(is_read_only()) begin
      uvm_report_error("resource", $sformatf("resource %s is read only -- cannot modify", get_name()));
      return;
    end

    // Set the modified bit and record the transaction only if the value
    // has actually changed.

    if (value_holder.read() == t)
      return;

    record_write_access(accessor);

    // set the value and set the dirty bit
    value_holder.write(this, t, accessor);

    modified = 1;
  endfunction

  virtual function void notify(string scope, string name, uvm_object accessor, string action_name, string inst_name = "");
    string accessor_name;

    if (accessor != null) accessor_name = accessor.get_full_name();

    value_holder.notify(scope, name, accessor_name, action_name, inst_name);
  endfunction : notify

endclass : uvm_extended_string_resource

class uvm_extended_string_config_db extends uvm_config_db#(string);

  static uvm_extended_string_config_db   imp;
  static uvm_config_db#(string) old_imp;

  virtual function uvm_resource#(string) m_new_resource(string field_name,
                                                        string inst_name);
    uvm_extended_string_resource result;

    result = new(field_name, inst_name);

    return result;
  endfunction

  virtual function bit m_is_resource_base_convertible(uvm_resource_base rsrc_base, uvm_resource#(T) r);
    return 0;
  endfunction

  virtual function bit m_get_compatible_value(uvm_component cntxt,
                                              string        inst_name,
                                              string        field_name,
                                              inout string  value,
                                              output bit    found);

    uvm_resource_pool            rp = uvm_resource_pool::get();
    uvm_resource_base            rsrc_base;
    uvm_resource_types::rsrc_q_t rq;
    uvm_extended_string_resource          r;

    if (uvm_resource_options::is_notifying() == 0)
      return 0;

    rq = rp.lookup_regex_names(inst_name, field_name, null);

    rsrc_base = rp.get_highest_precedence(rq);
    if ((rsrc_base == null) || ($cast(r,rsrc_base) == 0)) begin
      found = 0;
      return 1;
    end

    if(uvm_config_db_options::is_tracing())
      m_show_msg("CFGDB/GET", "Configuration","read", inst_name, field_name, cntxt, r);

    value = r.read(cntxt);
    found = 1;
    return 1;
  endfunction

  virtual function uvm_resource#(string) m_get_by_name(string inst_name,
                                                       string field_name,
                                                       bit    rpterr=1);
    return uvm_extended_string_resource::get_by_name(inst_name,field_name,rpterr);
  endfunction

  virtual function void m_notify(uvm_resource#(string) rsrc, 
                                 string                cntxt_name, 
                                 string                field_name, 
                                 uvm_object            accessor, 
                                 string                action_name, 
                                 string                inst_name);

    uvm_extended_string_resource r;

    assert ($cast(r, rsrc) == 1);

    if (uvm_resource_options::is_notifying())
        r.notify(cntxt_name, field_name, accessor, action_name, inst_name);
  endfunction

  static function bit get(uvm_component cntxt,
                          string        inst_name,
                          string        field_name,
                          inout string  value);
    bit result;
    uvm_config_db#(string) sav_imp;

    if (imp == null)
      imp = new;

    sav_imp = uvm_config_db#(string)::change_implementation(imp);

    result = uvm_config_db#(string)::get(cntxt, inst_name, field_name, value);

    uvm_config_db#(string)::restore_implementation(sav_imp);

    // Every time return implementation to be the generic one so that the direct access via uvm_config_db::get()
    // will behave consistently - before or after uvm_extended_singular_config_db::get()
    return result;
  endfunction

  static function void set(uvm_component cntxt,
                           string        inst_name,
                           string        field_name,
                           string        value);

    uvm_config_db#(string) sav_imp;

    if (imp == null)
      imp = new;
    sav_imp = uvm_config_db#(string)::change_implementation(imp);

    uvm_config_db#(string)::set(cntxt, inst_name, field_name, value);
    uvm_config_db#(string)::restore_implementation(sav_imp);

  endfunction

  static function void set_by_cntxt_name(string        cntxt_name,
                                         string        inst_name,
                                         string        field_name,
                                         string        value,
                                         int           cntxt_depth,
                                         uvm_component accessor = null);
    uvm_config_db#(string) sav_imp;
    if (imp == null)
      imp = new;

    sav_imp = uvm_config_db#(string)::change_implementation(imp);
    do_set(cntxt_name, inst_name, field_name, value, cntxt_depth, accessor);
    uvm_config_db#(string)::restore_implementation(sav_imp);
  endfunction
endclass

//--------------------
// ML Additions (END)
//--------------------
