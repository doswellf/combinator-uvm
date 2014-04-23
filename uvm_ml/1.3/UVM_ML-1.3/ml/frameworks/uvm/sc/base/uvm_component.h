//----------------------------------------------------------------------
//   Copyright 2009 Cadence Design Systems, Inc.
//   Copyright 2012 Advanced Micro Devices Inc.
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

/*! \file uvm_component.h
  \brief Base class for all UVM-SC components.
*/

#ifndef UVM_COMPONENT_H
#define UVM_COMPONENT_H

#include "base/uvm_typed.h"
#include "base/uvm_common_schedule.h"
#include "base/uvm_config_db.h"

#include "sysc/kernel/sc_module.h"
#include "sysc/kernel/sc_process_handle.h"

//////////////

namespace uvm {

// forward declaration of necessary classes.

class uvm_manager;
class uvm_phase;
class uvm_resource_base;

//------------------------------------------------------------------------------
//
// CLASS: uvm_component
//
// Base class for structural UVM elements.
// Derives from sc_module, and provides name, and hierarchy information.
//
//------------------------------------------------------------------------------


/*! \class uvm_component
  \brief Base class for structural UVM-SC elements.

  Derives from sc_module, and provides name, and hierarchy information.
*/
class uvm_component : public sc_core::sc_module, public uvm_typed {
public:
  friend class uvm_manager;

  //----------------------------------------------------------------------------
  // Constructors and destructor
  //----------------------------------------------------------------------------

  uvm_component(sc_core::sc_module_name nm);
  virtual ~uvm_component();

  //----------------------------------------------------------------------------
  // get_type_name   -- Required override
  //
  // Return the type name of this class - e.g., "my_component".
  // Inherits this pure virtual method from base class uvm_typed.
  //----------------------------------------------------------------------------

  virtual std::string get_type_name() const = 0;

  //----------------------------------------------------------------------------
  // Find out if a child with this leaf name exists.
  //----------------------------------------------------------------------------

  bool has_child(const char* leaf_name);

  int get_num_children();

  std::vector<uvm_component*> get_children();

  uvm_component* get_parent();
  
  //----------------------------------------------------------------------------
  // Set up configuration.
  //
  // The configuration settings will be stored in a table inside
  // this component.
  //----------------------------------------------------------------------------

  template <typename T> void set_config_int(
    const std::string& instname,
    const std::string& field,
    const T& val
  );
  void set_config_string(
    const std::string& instname,
    const std::string& field,
    const std::string& val
  );
  void set_config_object(
    const std::string& instname,
    const std::string& field,
    uvm_object* val,
    bool clone = true
  );

  //----------------------------------------------------------------------------
  // Get configurations.
  //
  // A get_config_xxx() call will look for a corresponding set_confiog_xxx()
  // call. The search will be done starting from the global configuration
  // table, and continuing in each component's configuration table in 
  // the parent hierarchy, in a top-down order.
  //----------------------------------------------------------------------------

  template <class T> bool get_config_int(
    const std::string& field,
    T& val
  );
  bool get_config_string(
    const std::string& field,
    std::string& val
  );
  bool uvm_get_config_string(
    const std::string& field,
    std::string& val
  );
  bool get_config_object(
    const std::string& field,
    uvm_object*& val,
    bool clone = true
  );

  //----------------------------------------------------------------------------
  // Interfaces to UVM factory.
  //
  // These interfaces provide convenient access to member methods of
  // uvm_factory.
  //----------------------------------------------------------------------------

  uvm_component* create_component(
    std::string type_name,
    std::string name
  );
  uvm_object* create_object(
    std::string type_name,
    std::string name = ""
  );

  void set_type_override(
    std::string orignal_type_name,
    std::string replacement_type_name,
    bool replace = true
  );
  void set_inst_override(
    std::string inst_path,    
    std::string orignal_type_name,
    std::string replacement_type_name
  );

  //----------------------------------------------------------------------------
  // Pre-run phase - build().
  //
  // build() is an alias for the existing sc_module phase
  // before_end_of_elaboration().
  // Other pre-run phases are inherited from sc_module.
  //----------------------------------------------------------------------------

  virtual void end_of_construction(); 
  virtual void build(); // synonym for before_end_of_elaboration;
  virtual void build_phase(uvm_phase *phase = NULL);
  virtual void connect_phase(uvm_phase *phase = NULL);
  virtual void before_end_of_elaboration(); 
  virtual void end_of_elaboration();
  virtual void end_of_elaboration_phase(uvm_phase *phase = NULL);
  virtual void start_of_simulation();
  virtual void start_of_simulation_phase(uvm_phase *phase = NULL);

  //----------------------------------------------------------------------------
  // Pre-run phase - connect()
  //
  // connect() is a UVM-SC specific phase
  // It does not exist in sc_module.
  // Other pre-run phases are inherited from sc_module.
  //----------------------------------------------------------------------------

  virtual void connect();

  //----------------------------------------------------------------------------
  // The run phase.
  //
  // The main thread of execution.
  // The component should not declare run as a thread process - it is
  // automatically spawned by uvm_component's constructor.
  // Run phase ends either by the uvm_stop_request() protocol
  // or by a timeout that can be customized by calling
  // uvm_set_global_timeout().
  //----------------------------------------------------------------------------

  virtual void run_phase(uvm_phase *phase); 
  virtual void run(); 
  virtual void reset_phase(uvm_phase *phase); 
  virtual void configure_phase(uvm_phase *phase); 
  virtual void main_phase(uvm_phase *phase); 
  virtual void shutdown_phase(uvm_phase *phase); 

  //----------------------------------------------------------------------------
  // Stop mechanism to veto termination triggered by uvm_stop_request().
  //
  // If enable_stop_interrupt() returns true, then the stop() member method 
  // will be spawned as a thread process when uvm_stop_request() is 
  // invoked in the design.
  // Simulation will not stop until all the stop process return.
  // The component should not declare stop() explicitly as a thread process.
  //----------------------------------------------------------------------------

  virtual void stop(); 
  virtual bool enable_stop_interrupt();

  //----------------------------------------------------------------------------
  // Post-run phases.
  //
  // These phases will trigger after the run phase ends.
  // Usually after the post-run phases are over, sc_stop() is  
  // issued, which wll trigger the end_of_simulation() phase also. 
  //----------------------------------------------------------------------------

  virtual void extract_phase(uvm_phase *phase);
  virtual void extract();
  virtual void check_phase(uvm_phase *phase);
  virtual void check();
  virtual void report_phase(uvm_phase *phase);
  virtual void report();
  virtual void final_phase(uvm_phase *phase);

  virtual void phase_started(uvm_phase *phase);
  virtual void phase_execute(uvm_phase *phase);
  virtual void phase_ready_to_end(uvm_phase *phase);
  virtual void phase_ended(uvm_phase *phase);

  //----------------------------------------------------------------------------
  // Issue process control constructs on run() process.
  //
  // For those simulators that support process control constructs, 
  // the corresponding construct will be issued on the run() process
  // handle. A value of false is returned if a simulator does not
  // support process control constructs.
  //----------------------------------------------------------------------------

  virtual bool kill();
  virtual bool reset();
  virtual bool suspend();
  virtual bool resume();
  virtual bool disable();
  virtual bool enable();
  virtual bool sync_reset_on();
  virtual bool sync_reset_off();
  // cannot use virtual with templated member method
  template <typename T>
  //virtual bool throw_it(T& t);
  bool throw_it(T& t);

  //----------------------------------------------------------------------------
  // Objection interface
  //----------------------------------------------------------------------------

  // Function: raised
  //
  // The raised callback is called when a decendant of the component instance
  // raises the specfied ~objection~. The ~source_obj~ is the object which
  // originally raised the object. ~count~ is an optional count that was used
  // to indicate a number of objections which were raised.

  //virtual void raised (uvm_objection *objection, uvm_component *source_comp, int count) {};


  // Function: dropped
  //
  // The dropped callback is called when a decendant of the component instance
  // raises the specfied ~objection~. The ~source_obj~ is the object which
  // originally dropped the object. ~count~ is an optional count that was used
  // to indicate a number of objections which were dropped.

  //virtual void dropped (uvm_objection* objection, uvm_component* source_comp, int count) {};


  // Function: all_dropped
  //
  // The all_dropped callback is called when a decendant of the component instance
  // raises the specfied ~objection~. The ~source_obj~ is the object which
  // originally all_dropped the object. ~count~ is an optional count that was used
  // to indicate a number of objections which were dropped. This callback is
  // time-consuming and the all_dropped conditional will not be propagated
  // up to the object's parent until the callback returns.

  //virtual void all_dropped (uvm_objection* objection, uvm_component* source_comp, int count) {};

  void set_run_handle(sc_core::sc_process_handle h);
  void set_reset_handle(sc_core::sc_process_handle h);
  void set_configure_handle(sc_core::sc_process_handle h);
  void set_main_handle(sc_core::sc_process_handle h);
  void set_shutdown_handle(sc_core::sc_process_handle h);

  virtual void config_callback(std::string cntxt, std::string inst_name, std::string field_name, uvm_resource_base * rsrc);
  virtual void rsrc_callback(uvm_rsrc_action action, std::string inst_name, std::string field_name, uvm_resource_base * rsrc);

protected:
  sc_core::sc_process_handle m_run_handle;
  sc_core::sc_process_handle m_reset_handle;
  sc_core::sc_process_handle m_configure_handle;
  sc_core::sc_process_handle m_main_handle;
  sc_core::sc_process_handle m_shutdown_handle;

private: 
  std::string prepend_name(std::string s);
};

//////////////

//------------------------------------------------------------------------------
// Templated functions necessary to support get_config_int()
//
//------------------------------------------------------------------------------
#define uvm_get_nbits_type(t) \
inline unsigned int uvm_get_nbits(const t& v) { \
  return (8 * sizeof(v)); \
}
uvm_get_nbits_type(bool)
uvm_get_nbits_type(char)
uvm_get_nbits_type(sc_dt::uchar)
uvm_get_nbits_type(short)
uvm_get_nbits_type(ushort)
uvm_get_nbits_type(int)
uvm_get_nbits_type(uint)
uvm_get_nbits_type(long)
uvm_get_nbits_type(ulong)
uvm_get_nbits_type(sc_dt::int64)
uvm_get_nbits_type(sc_dt::uint64)

inline unsigned int uvm_get_nbits(const sc_dt::sc_bv_base &v) {
  return v.length();
}

inline unsigned int uvm_get_nbits(const sc_dt::sc_logic &v) {
  return 1;
}

template <typename T> void uvm_convert_from_bv(T& v, sc_dt::sc_bv_base bv) {
  v = bv; 
}
inline void uvm_convert_from_bv(sc_dt::sc_logic& v, const sc_dt::sc_bv_base& bv) { \
  v = bv.get_bit(0);
}
#define uvm_convert_from_bv_int_type(t) \
inline void uvm_convert_from_bv(t& v, const sc_dt::sc_bv_base& bv) { \
  sc_dt::uint64 u = bv.to_uint64(); \
  v = u;  \
}
uvm_convert_from_bv_int_type(bool)
uvm_convert_from_bv_int_type(char)
uvm_convert_from_bv_int_type(sc_dt::uchar)
uvm_convert_from_bv_int_type(short)
uvm_convert_from_bv_int_type(ushort)
uvm_convert_from_bv_int_type(int)
uvm_convert_from_bv_int_type(uint)
uvm_convert_from_bv_int_type(long)
uvm_convert_from_bv_int_type(ulong)
uvm_convert_from_bv_int_type(sc_dt::int64)
uvm_convert_from_bv_int_type(sc_dt::uint64)
// and similarly for char, unsigned, ...

/////////////

//------------------------------------------------------------------------------
// Templated functions necessary to support set_config_int()
//
//------------------------------------------------------------------------------

template <typename T> sc_dt::sc_bv_base uvm_convert_to_bv(const T& v) {
  int nbits = uvm_get_nbits(v);
  sc_dt::sc_bv_base bv(nbits);
  bv = v;
  return bv;
}
inline sc_dt::sc_bv_base uvm_convert_to_bv(const sc_dt::sc_logic& v) {
  sc_dt::sc_bv_base bv(1);
  bv.set_bit(0,v.value());
  return bv;
}

/////////////

template <typename T> void uvm_component::set_config_int(
  const std::string& instname,
  const std::string& field,
  const T& val
) {

  int nbits = uvm_get_nbits(val);
  sc_dt::sc_bv_base bv(nbits);

  bv = uvm_convert_to_bv(val);
  uvm_config_db<sc_dt::sc_bv_base>::set(this, instname, field, bv);
}

template <typename T> bool uvm_component::get_config_int(
  const std::string& field,
  T& val
) {
  bool result;
  int nbits = uvm_get_nbits(val);
  sc_dt::sc_bv_base bv(nbits);

  result =  uvm_config_db<sc_dt::sc_bv_base >::get(this, "", field, bv);
  if (result)
    uvm_convert_from_bv(val, bv);

  return result;
}

//////////////

//------------------------------------------------------------------------------
// Registration macros to register an uvm_component with the factory.
// 
// A registration macro should be invoked outside the uvm_component class
// declaration.
// A registration macro registers the given uvm_component with the factory, and
// defines the get_type_name() member method of the registered component.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// Use the macro below to register a simple non-templated uvm_component.
// The macro argument is the name of the class.
// The registered name with the factory is the same as the macro argument.
//------------------------------------------------------------------------------

#define UVM_COMPONENT_REGISTER(t) \
static int uvm_component_register_dummy_##t = \
  uvm::uvm_factory::register_component_creator( #t,new t::uvm_component_creator_##t()); \
inline std::string t::get_type_name() const { return #t; }

//------------------------------------------------------------------------------
// Use the macro below to register a simple non-templated uvm_component,
// with a different registered name (first argument) than its
// class name (second argument).
// The registered name with the factory is the same as the first macro argument.
//------------------------------------------------------------------------------

#define UVM_COMPONENT_REGISTER_ALIAS(name,t) \
static int uvm_component_register_dummy_##name##_##t = \
  uvm::uvm_factory::register_component_creator( #name,new t::uvm_component_creator_##t()); \
inline std::string t::get_type_name() const { return #name; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_components with
// one template parameter.
// The first macro argument is the class name, and the second macro argument
// is a specific value of the template parameter.
// Example usage: "UVM_COMPONENT_REGISTER_T(mycomp, int)".
// The registered name with the factory is a concatenation of the first
// and second arguments, separated by "_".
// e.g., "mycomp_int".
//------------------------------------------------------------------------------

#define UVM_COMPONENT_REGISTER_T(t,T) \
static int uvm_component_register_dummy_##t##_##T = \
  uvm::uvm_factory::register_component_creator( #t "_" #T, new t<T>::uvm_component_creator_##t()); \
template<> inline std::string t<T>::get_type_name() const { return #t "_" #T; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_components with
// one template parameter, when you do not want the default registered name.
// Specify the alternate registration name as the first macro argument.
// Example usage: "UVM_COMPONENT_REGISTER_T_ALIAS(myname, mycomp, int)".
// The registered name with the factory is the same as the first macro 
// argument.
//------------------------------------------------------------------------------

#define UVM_COMPONENT_REGISTER_T_ALIAS(name,t,T) \
static int uvm_component_register_dummy_##name##_##t = \
  uvm::uvm_factory::register_component_creator( #name, new t<T>::uvm_component_creator_##t()); \
template<> inline std::string t<T>::get_type_name() const { return #name; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_components with
// two template parameters.
// The first macro argument is the class name. 
// The second and third macro arguments are specific values of the
// two template parameters.
// Example usage: "UVM_COMPONENT_REGISTER_T2(myothercomp, int, int)".
// The registered name with the factory is a concatenation of the first,
// second, and third arguments, separated by "_". 
// e.g., "myothercomp_int_int".
//------------------------------------------------------------------------------

#define UVM_COMPONENT_REGISTER_T2(t,T1,T2) \
static int uvm_component_register_dummy_##t##_##T1##_##T2 = \
  uvm::uvm_factory::register_component_creator( #t "_" #T1 "_" #T2, new t<T1,T2>::uvm_component_creator_##t()); \
template<> inline std::string t<T1,T2>::get_type_name() const { return #t "_" #T1 "_" #T2; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_components with 
// two template parameters, when you do not want the default registered name.
// Specify the alternate registration name as the first macro argument.
// Example usage: 
//   "UVM_COMPONENT_REGISTER_T2_ALIAS(myname, myothercomp, int, int)".
// The registered name with the factory is the same as the first macro argument.
//------------------------------------------------------------------------------

#define UVM_COMPONENT_REGISTER_T2_ALIAS(name,t,T1,T2) \
static int uvm_component_register_dummy_##name##_##t = \
  uvm::uvm_factory::register_component_creator( #name, new t<T1,T2>::uvm_component_creator_##t()); \
template<> inline std::string t<T1,T2>::get_type_name() const { return #name; }

//------------------------------------------------------------------------------
// Utility macro to instrument an uvm_component such that it can be registered
// with the factory.
// 
// The utility macro should be invoked inside the uvm_component class
// declaration.
// The utility macro declares
// - the uvm_component_creator_<classname> class used by the factory
//   to create an instance of this component.
// - the get_type_name() member method inside the uvm_component class.
//------------------------------------------------------------------------------

#define UVM_COMPONENT_UTILS(t) \
class uvm_component_creator_##t : public uvm::uvm_component_creator { \
public: \
  uvm::uvm_component* create(const std::string& name) { \
    uvm::uvm_component* _ncsc_comp = new t(name.c_str()); \
    return _ncsc_comp; \
  } \
}; \
virtual std::string get_type_name() const;

//////////////

} // namespace uvm

#endif
