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

/*! \file uvm_component.cpp
  \brief Base class for all UVM-SC components.
*/

#define SC_INCLUDE_DYNAMIC_PROCESSES
#include "systemc.h"

#include "base/uvm_component.h"
#include "base/uvm_factory.h"
#include "base/uvm_manager.h"
#include "base/uvm_resource_base.h"

#include "uvm_imp_spec_macros.h"

using namespace std;
using namespace sc_core;

namespace uvm {

//------------------------------------------------------------------------------
//
// uvm_component
//
//------------------------------------------------------------------------------

static bool global_timeout_spawned_ = false;

#include "uvm_component_spec.cpp"

// constructor of uvm_component spawns run() member method as a thread process

uvm_component::uvm_component(sc_module_name nm) : sc_module(nm) { 

  uvm_common_schedule* pcommon_schedule = get_uvm_common_schedule();
  pcommon_schedule->register_callback(this);

  // TODO: should all component default to be part of UVM schedule?
  uvm_common_schedule* puvm_schedule = get_uvm_schedule();
  puvm_schedule->register_callback(this);

  if (!global_timeout_spawned_) {
    // spawn thread that will wait for m_global_timeout to expire
    sc_spawn_options o;

    MARK_THREAD_INVISIBLE(o);
    sc_spawn(sc_bind(&uvm_manager::wait_for_global_timeout, get_uvm_manager()),
             "uvm_wait_for_global_timeout",
             &o
    );
    global_timeout_spawned_ = true;
  }
}

uvm_component::~uvm_component() { }

bool uvm_component::has_child(const char* leaf_name) {
  string full_name = prepend_name(string(leaf_name));
  if (sc_find_object(full_name.c_str())) 
    return true;
  return false; 
}

void uvm_component::set_config_string(
  const string& instname,
  const string& field,
  const string& val
) {
  uvm_config_db<string>::set(this, instname, field, val);
}

void uvm_component::set_config_object(
  const string& instname,
  const string& field,
  uvm_object* val,
  bool clone 
) {
  // TODO: clone
  uvm_config_db<uvm_object *>::set(this, instname, field, val);
}

bool uvm_component::get_config_string(
  const string& field,
  string& val
) {
  return uvm_config_db<string>::get(this, "", field, val);
}

bool uvm_component::uvm_get_config_string(
  const string& field,
  string& val
) {
  return uvm_config_db<string>::get(this, "", field, val);
}


bool uvm_component::get_config_object(
  const string& field,
  uvm_object*& val,
  bool clone
) {
  val = NULL; // must initialize it because the template can not assign 0
  return uvm_config_db<uvm_object *>::get(this, "", field, val);
}

uvm_component* uvm_component::create_component(
  std::string type_name,
  std::string leaf
) {
  return uvm_factory::create_component(type_name, std::string(name()), leaf);
}

uvm_object* uvm_component::create_object(
  std::string type_name,
  std::string leaf 
) {
  return uvm_factory::create_uvm_object(type_name, std::string(name()), leaf);
}

void uvm_component::set_type_override(
  std::string original_type_name,
  std::string replacement_type_name,
  bool replace 
) {
  uvm_factory::set_type_override(
    original_type_name, replacement_type_name, replace
  );
}

void uvm_component::set_inst_override(
  std::string inst_path,    
  std::string original_type_name,
  std::string replacement_type_name
) {
  std::string path = prepend_name(inst_path);
  uvm_factory::set_inst_override(
    path, original_type_name, replacement_type_name
  );
}

// called by SC kernel

void uvm_component::before_end_of_elaboration() { 
}

void uvm_component::connect_phase(uvm_phase *phase) {
  connect();
}

void uvm_component::build_phase(uvm_phase *phase) { 
  build();
}

// called by before_end_of_elaboration()

void uvm_component::build() { 
  end_of_construction();
}

// called by build()

void uvm_component::end_of_construction() { 
}

void uvm_component::connect() {
}

void uvm_component::end_of_elaboration() { 
}

void uvm_component::end_of_elaboration_phase(uvm_phase* phase) { 
  end_of_elaboration();
}

void uvm_component::start_of_simulation() { 
}

void uvm_component::start_of_simulation_phase(uvm_phase* phase) { 
  start_of_simulation();
}


void uvm_component::run_phase(uvm_phase* phase) { 
  phase->barrier.raise_barrier();
  run();
  phase->barrier.drop_barrier();
}

void uvm_component::run() { 
}

void uvm_component::reset_phase(uvm_phase* phase) { 
}

void uvm_component::configure_phase(uvm_phase* phase) { 
}

void uvm_component::main_phase(uvm_phase* phase) { 
}

void uvm_component::shutdown_phase(uvm_phase* phase) { 
}

void uvm_component::stop() { 
}

void uvm_component::extract_phase(uvm_phase* phase) { 
  extract();
}

void uvm_component::extract() { 
}

void uvm_component::check_phase(uvm_phase* phase) { 
  check();
}

void uvm_component::check() { 
}

void uvm_component::report_phase(uvm_phase* phase) { 
  report();
}

void uvm_component::report() { 
}

void uvm_component::final_phase(uvm_phase* phase) { 
}

void uvm_component::phase_started(uvm_phase* phase) { 
}

void uvm_component::phase_execute(uvm_phase* phase) { 

}

void uvm_component::phase_ready_to_end(uvm_phase* phase) { 
}

void uvm_component::phase_ended(uvm_phase* phase) { 
}

//
bool uvm_component::enable_stop_interrupt() {
  return false;
}

// internal methods

void uvm_component::set_run_handle(sc_process_handle h) {
  m_run_handle = h;
}

void uvm_component::set_reset_handle(sc_process_handle h) {
  m_reset_handle = h;
}

void uvm_component::set_configure_handle(sc_process_handle h) {
  m_configure_handle = h;
}

void uvm_component::set_main_handle(sc_process_handle h) {
  m_main_handle = h;
}

void uvm_component::set_shutdown_handle(sc_process_handle h) {
  m_shutdown_handle = h;
}

string uvm_component::prepend_name(string s) {
  string n = name();
  if (s != "") {
    n += string(".");
    n += s;
  }
  return n;
}

//------------------------------------------------------------------------------
// Function: get_num_children
//  Returns the number of child components this components has.
//
// Returns:
//  int - number of children the components has.
//------------------------------------------------------------------------------
int uvm_component::get_num_children() {
  std::vector<uvm_component*> child_vec;
  child_vec = get_children();

  return child_vec.size();
}

//------------------------------------------------------------------------------
// Function: get_children
//  Returns vector of pointers to children
//
// Returns:
//  vec - vector of pointers to children
//------------------------------------------------------------------------------
std::vector<uvm_component*> uvm_component::get_children() {
  std::vector<sc_object*> child_vec;
  std::vector<uvm_component*> child_comp_vec;
  uvm_component* comp = NULL;
  child_vec = get_child_objects();


  for (int i = 0; i < child_vec.size(); i++)
  {
    comp = DCAST<uvm_component*>(child_vec[i]);
    if (comp != NULL)
      child_comp_vec.push_back(comp);
  }

  return child_comp_vec;
}


//------------------------------------------------------------------------------
// Function: get_parent
//  Returns a pointer to the parent
//
// Returns:
//  int - number of children the components has.
//------------------------------------------------------------------------------
uvm_component* uvm_component::get_parent() {
  uvm_component*      uvm_comp;
  sc_core::sc_object* sc_obj = sc_core::sc_module::get_parent();
  
  uvm_comp = DCAST<uvm_component*>(sc_obj);

  return uvm_comp;
}

//------------------------------------------------------------------------------
// Function: config_callback
//  Callback function called when config_db<>.set gets executed
//
//------------------------------------------------------------------------------
void uvm_component::config_callback(std::string cntxt, std::string inst_name, std::string field_name, uvm_resource_base * rsrc)
{
}

//------------------------------------------------------------------------------
// Function: rsrc_callback
//  Callback function called when config_db<>.set gets executed
//
//------------------------------------------------------------------------------
void uvm_component::rsrc_callback(uvm_rsrc_action action, std::string inst_name, std::string field_name, uvm_resource_base * rsrc)
{
}


} // namespace uvm
