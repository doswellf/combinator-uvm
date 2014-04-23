//----------------------------------------------------------------------
//   Copyright 2011 Cypress Semiconductor
//   Copyright 2010-2011 Mentor Graphics Corporation
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

typedef class uvm_phase;

//----------------------------------------------------------------------
// Title: UVM Configuration Database
//
// Topic: Intro
//
// The <uvm_config_db> class provides a convenience interface 
// on top of the <uvm_resource_db> to simplify the basic interface
// that is used for configuring <uvm_component> instances.
//
// If the run-time ~+UVM_CONFIG_DB_TRACE~ command line option is specified,
// all configuration DB accesses (read and write) are displayed.
//----------------------------------------------------------------------

//Internal class for config waiters
class m_uvm_waiter;
  string inst_name;
  string field_name;
  event trigger;
  function new (string inst_name, string field_name);
    this.inst_name = inst_name;
    this.field_name = field_name;
  endfunction
endclass

typedef class uvm_config_db_options;

//----------------------------------------------------------------------
// class: uvm_config_db
//
// All of the functions in uvm_config_db#(T) are static, so they
// must be called using the :: operator.  For example:
//
//|  uvm_config_db#(int)::set(this, "*", "A");
//
// The parameter value "int" identifies the configuration type as
// an int property.  
//
// The <set> and <get> methods provide the same api and
// semantics as the set/get_config_* functions in <uvm_component>.
//----------------------------------------------------------------------
class uvm_config_db#(type T=int) extends uvm_resource_db#(T);

  // Internal lookup of config settings so they can be reused
  // The context has a pool that is keyed by the inst/field name.
//--------------------
// ML Additions (START)
//--------------------

  static uvm_config_db#(T) m_generic_implementation;
  static uvm_config_db#(T) m_implementation;

  static function void set_implementation();
    if (m_generic_implementation == null) // First time call
      m_generic_implementation = new;

    if (m_implementation == null) 
      m_implementation = m_generic_implementation;
  endfunction

  static function uvm_config_db#(T) change_implementation(uvm_config_db#(T) imp);
    uvm_config_db#(T) old_m_implementation = m_implementation;
    m_implementation = imp;
    return old_m_implementation;
  endfunction

  static function void restore_implementation(uvm_config_db#(T) old_m_implementation);
    m_implementation = old_m_implementation;
  endfunction

  virtual function uvm_resource#(T) m_new_resource(string field_name,
                                                   string inst_name);
    uvm_resource#(T) result;

    result = new(field_name, inst_name);
    return result;
  endfunction

  virtual function bit m_is_resource_base_convertible(uvm_resource_base rsrc_base, uvm_resource#(T) r);
    return 0;
  endfunction

  virtual function bit m_get_compatible_value(uvm_component cntxt,
                                              string        inst_name,
                                              string        field_name,
                                              inout T       value,
                                              output bit    found);
    return 0;
  endfunction

  virtual function uvm_resource#(T) m_get_by_name(string inst_name,
                                                  string field_name,
                                                  bit    rpterr=1);
    return uvm_resource#(T)::get_by_name(inst_name,field_name,rpterr);
  endfunction

  virtual function void m_notify(uvm_resource#(T) rsrc, 
                                 string           cntxt_name, 
                                 string           field_name, 
                                 uvm_object       accessor, 
                                 string           action_name, 
                                 string           inst_name);
  endfunction

  //  static uvm_pool#(string,uvm_resource#(T)) m_rsc[uvm_component];
  static uvm_pool#(string,uvm_resource_base) m_rsc[string];
//--------------------
// ML Additions (END)
//--------------------

  // Internal waiter list for wait_modified
  static local uvm_queue#(m_uvm_waiter) m_waiters[string];

  // function: get
  //
  // Get the value for ~field_name~ in ~inst_name~, using component ~cntxt~ as 
  // the starting search point. ~inst_name~ is an explicit instance name 
  // relative to ~cntxt~ and may be an empty string if the ~cntxt~ is the
  // instance that the configuration object applies to. ~field_name~
  // is the specific field in the scope that is being searched for.
  //
  // The basic get_config_* methods from <uvm_component> are mapped to 
  // this function as:
  //
  //| get_config_int(...) => uvm_config_db#(uvm_bitstream_t)::get(cntxt,...)
  //| get_config_string(...) => uvm_config_db#(string)::get(cntxt,...)
  //| get_config_object(...) => uvm_config_db#(uvm_object)::get(cntxt,...)

  static function bit get(uvm_component cntxt,
                          string inst_name,
                          string field_name,
                          inout T value);
//TBD: add file/line
    int unsigned p;
    uvm_resource#(T) r, rt;
    uvm_resource_pool rp = uvm_resource_pool::get();
    uvm_resource_types::rsrc_q_t rq;

    if(cntxt == null) 
      cntxt = uvm_root::get();
    if(inst_name == "") 
      inst_name = cntxt.get_full_name();
    else if(cntxt.get_full_name() != "") 
      inst_name = {cntxt.get_full_name(), ".", inst_name};
 
//----------------------
// ML Additions (START)
//----------------------
    set_implementation();
    begin
      bit result;
      if (m_implementation.m_get_compatible_value(cntxt, inst_name, field_name, value, result))
        return result;
    end
//--------------------
// ML Additions (END)
//--------------------

    rq = rp.lookup_regex_names(inst_name, field_name, uvm_resource#(T)::get_type());
    r = uvm_resource#(T)::get_highest_precedence(rq);
    
    if(uvm_config_db_options::is_tracing())
      m_show_msg("CFGDB/GET", "Configuration","read", inst_name, field_name, cntxt, r);

    if(r == null)
      return 0;

    value = r.read(cntxt);

    return 1;
  endfunction

//----------------------
// ML Additions (START)
//----------------------
  static function void do_set(string        cntxt_name,
                              string        inst_name,
                              string        field_name,
                              T             value,
                              int           cntxt_depth,
                              uvm_component accessor = null);

    uvm_root top;
    uvm_phase curr_phase;
    uvm_resource#(T) r;
    bit exists;
    string lookup;
    uvm_pool#(string,uvm_resource_base) pool;

    string orig_inst_name;
    string rstate;     

    //take care of random stability during allocation
    process p = process::self();
    if (p)
        rstate = p.get_randstate();

    top = uvm_root::get();
    curr_phase = top.m_current_phase;

    orig_inst_name = inst_name;

    if(inst_name == "") 
      inst_name = cntxt_name;
    else if(cntxt_name != "") 
      inst_name = {cntxt_name, ".", inst_name};

    if(!m_rsc.exists(cntxt_name)) begin
      m_rsc[cntxt_name] = new;
    end
    pool = m_rsc[cntxt_name];

    // Insert the token in the middle to prevent cache
    // oddities like i=foobar,f=xyz and i=foo,f=barxyz.
    // Can't just use '.', because '.' isn't illegal
    // in field names
    lookup = {inst_name, "__M_UVM__", field_name};

    if(!pool.exists(lookup)) begin
//----------------------
// ML Additions (START)
//----------------------
       // r = new(field_name, inst_name); // ML-related modification
       r = m_implementation.m_new_resource(field_name, inst_name);
//--------------------
// ML Additions (END)
//--------------------
       pool.add(lookup, r);
    end
    else begin
      uvm_resource_base rsrc_base = pool.get(lookup);
      if (uvm_resource#(T)::get_type() == rsrc_base.get_type_handle()) begin 
        // exact match
        $cast(r, rsrc_base);
        exists = 1;
      end
      else begin
        if (m_implementation.m_is_resource_base_convertible(rsrc_base, r))
          exists = 1;
      end
      if (r == null) begin
        string msg;
        $sformat(msg, "Configuration element with name %s.%s and context %s in the configuration database exists but has incompatible value type", inst_name, field_name, cntxt_name);
        uvm_report_fatal("CONFIGTYPEINC", msg);
      end
    end
      
    if(curr_phase != null && curr_phase.get_name() == "build")
      r.precedence -= cntxt_depth;

    r.write(value, accessor);

    if(exists) begin
      uvm_resource_pool rp = uvm_resource_pool::get();
      rp.set_priority_name(r, uvm_resource_types::PRI_HIGH);
    end
    else begin
      //Doesn't exist yet, so put it in resource db at the head.
      r.set_override();
    end

    //trigger any waiters
    if(m_waiters.exists(field_name)) begin
      m_uvm_waiter w;
      for(int i=0; i<m_waiters[field_name].size(); ++i) begin
        w = m_waiters[field_name].get(i);
        if(uvm_re_match(uvm_glob_to_re(inst_name),w.inst_name) == 0)
           ->w.trigger;  
      end
    end

    if (p)
        p.set_randstate(rstate);

    m_implementation.m_notify(r, cntxt_name, field_name, accessor, "CONFIG_SET", orig_inst_name);

    if(uvm_config_db_options::is_tracing())
      m_show_msg("CFGDB/SET", "Configuration","set", inst_name, field_name, accessor, r);

  endfunction : do_set

//--------------------
// ML Additions (END)
//--------------------

  // function: set 
  //
  // Create a new or update an existing configuration setting for
  // ~field_name~ in ~inst_name~ from ~cntxt~.
  // The setting is made at ~cntxt~, with the full name of ~cntxt~ 
  // added to the ~inst_name~. If ~cntxt~ is null then ~inst_name~
  // provides the complete scope information of the setting.
  // ~field_name~ is the target field. Both ~inst_name~ and ~field_name~
  // may be glob style or regular expression style expressions.
  //
  // If a setting is made at build time, the ~cntxt~ hierarchy is
  // used to determine the setting's precedence in the database.
  // Settings from hierarchically higher levels have higher
  // precedence. Settings from the same level of hierarchy have
  // a last setting wins semantic. A precedence setting of 
  // <uvm_resource_base::default_precedence>  is used for uvm_top, and 
  // each hierarcical level below the top is decremented by 1.
  //
  // After build time, all settings use the default precedence and thus
  // have a last wins semantic. So, if at run time, a low level 
  // component makes a runtime setting of some field, that setting 
  // will have precedence over a setting from the test level that was 
  // made earlier in the simulation.
  //
  // The basic set_config_* methods from <uvm_component> are mapped to 
  // this function as:
  //
  //| set_config_int(...) => uvm_config_db#(uvm_bitstream_t)::set(cntxt,...)
  //| set_config_string(...) => uvm_config_db#(string)::set(cntxt,...)
  //| set_config_object(...) => uvm_config_db#(uvm_object)::set(cntxt,...)

  static function void set(uvm_component cntxt,
                           string inst_name,
                           string field_name,
                           T value);

//----------------------
// ML Additions (START)
//----------------------
    string cntxt_name;
    int    cntxt_depth;

    if (cntxt == null) 
      cntxt = uvm_root::get();

    cntxt_name = cntxt.get_full_name();
    cntxt_depth = cntxt.get_depth();

    set_implementation();
    do_set(cntxt_name, inst_name, field_name, value, cntxt_depth, cntxt);

//--------------------
// ML Additions (END)
//--------------------
  endfunction


  // function: exists
  //
  // Check if a value for ~field_name~ is available in ~inst_name~, using
  // component ~cntxt~ as the starting search point. ~inst_name~ is an explicit
  // instance name relative to ~cntxt~ and may be an empty string if the
  // ~cntxt~ is the instance that the configuration object applies to.
  // ~field_name~ is the specific field in the scope that is being searched for.
  // The ~spell_chk~ arg can be set to 1 to turn spell checking on if it
  // is expected that the field should exist in the database. The function
  // returns 1 if a config parameter exists and 0 if it doesn't exist.
  //

  static function bit exists(uvm_component cntxt, string inst_name,
      string field_name, bit spell_chk=0);

    if(cntxt == null)
      cntxt = uvm_root::get();
    if(inst_name == "")
      inst_name = cntxt.get_full_name();
    else if(cntxt.get_full_name() != "")
      inst_name = {cntxt.get_full_name(), ".", inst_name};

//----------------------
// ML Additions (START)
//----------------------
    // return (uvm_resource_db#(T)::get_by_name(inst_name,field_name,spell_chk) != null);
    set_implementation();
    return (m_implementation.m_get_by_name(inst_name,field_name,spell_chk) != null);
//--------------------
// ML Additions (END)
//--------------------
  endfunction


  // Function: wait_modified
  //
  // Wait for a configuration setting to be set for ~field_name~
  // in ~cntxt~ and ~inst_name~. The task blocks until a new configuration
  // setting is applied that effects the specified field.

  static task wait_modified(uvm_component cntxt, string inst_name,
      string field_name);
    process p = process::self();
    string rstate = p.get_randstate();
    m_uvm_waiter waiter;

    if(cntxt == null)
      cntxt = uvm_root::get();
    if(cntxt != uvm_root::get()) begin
      if(inst_name != "")
        inst_name = {cntxt.get_full_name(),".",inst_name};
      else
        inst_name = cntxt.get_full_name();
    end

    waiter = new(inst_name, field_name);

    if(!m_waiters.exists(field_name))
      m_waiters[field_name] = new;
    m_waiters[field_name].push_back(waiter);

    p.set_randstate(rstate);

    // wait on the waiter to trigger
    @waiter.trigger;
  
    // Remove the waiter from the waiter list 
    for(int i=0; i<m_waiters[field_name].size(); ++i) begin
      if(m_waiters[field_name].get(i) == waiter) begin
        m_waiters[field_name].delete(i);
        break;
      end
    end 
  endtask

endclass

typedef uvm_config_db#(uvm_object_wrapper) uvm_config_wrapper;


//----------------------------------------------------------------------
// Class: uvm_config_db_options
//
// Provides a namespace for managing options for the
// configuration DB facility.  The only thing allowed in this class is static
// local data members and static functions for manipulating and
// retrieving the value of the data members.  The static local data
// members represent options and settings that control the behavior of
// the configuration DB facility.

// Options include:
//
//  * tracing:  on/off
//
//    The default for tracing is off.
//
//----------------------------------------------------------------------
class uvm_config_db_options;
   
  static local bit ready;
  static local bit tracing;

  // Function: turn_on_tracing
  //
  // Turn tracing on for the configuration database. This causes all
  // reads and writes to the database to display information about
  // the accesses. Tracing is off by default.
  //
  // This method is implicitly called by the ~+UVM_CONFIG_DB_TRACE~.

  static function void turn_on_tracing();
     if (!ready) init();
    tracing = 1;
  endfunction

  // Function: turn_off_tracing
  //
  // Turn tracing off for the configuration database.

  static function void turn_off_tracing();
     if (!ready) init();
    tracing = 0;
  endfunction

  // Function: is_tracing
  //
  // Returns 1 if the tracing facility is on and 0 if it is off.

  static function bit is_tracing();
    if (!ready) init();
    return tracing;
  endfunction


  static local function void init();
     uvm_cmdline_processor clp;
     string trace_args[$];
     
     clp = uvm_cmdline_processor::get_inst();

     if (clp.get_arg_matches("+UVM_CONFIG_DB_TRACE", trace_args)) begin
        tracing = 1;
     end

     ready = 1;
  endfunction

endclass
