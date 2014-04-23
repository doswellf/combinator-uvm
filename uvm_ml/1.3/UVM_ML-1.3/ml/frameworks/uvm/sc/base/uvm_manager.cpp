//----------------------------------------------------------------------
//   Copyright 2009 Cadence Design Systems, Inc.
//   Copyright 2012 Advance Micro Devices, Inc
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

/*! \file uvm_manager.cpp
  \brief Central manager of UVM-SC global functions.
*/

#define SC_INCLUDE_DYNAMIC_PROCESSES
#include "systemc.h"
#include <packages/boost/include/regex.hpp>
#include "base/uvm_manager.h"
#include "base/uvm_ids.h"
#include "base/uvm_component.h"
#include "uvm_imp_spec_macros.h"

using namespace sc_core;

namespace uvm {

//------------------------------------------------------------------------------
//
// uvm_manager
//
// Internal implementation class.
//
//------------------------------------------------------------------------------

uvm_manager* uvm_manager::m_mgr = 0;

uvm_manager* uvm_manager::get_manager() {
  if (m_mgr == 0) {
    m_mgr = new uvm_manager();
  }
  return m_mgr;
}

uvm_manager::uvm_manager() {
  m_stop_mode = UVM_SC_STOP;

  sc_time max_time; // the time at which sc_start() returns
  sc_time smallest_time = sc_get_time_resolution();

  max_time = SC_MAX_TIME;

  // make the UVM timeouts be slightly less than when sc_start() returns
  // such that UVM is able to end the run phase
  m_global_timeout = max_time - smallest_time;
  m_stop_timeout = max_time - smallest_time;
}
 
uvm_manager::~uvm_manager() {
}


//------------------------------------------------------------------------------
// Function: find_component
//   Regular expression search for UVM components base on instance name.  Returns
//   the first match found.
//
// Parameters;
//  @param name - name to search for
//
// Returns:
//  @param comp - pointer to uvm component found, NULL if no matching.
//------------------------------------------------------------------------------
uvm_component* uvm_manager::find_component(const char* name) {
    bool           bfound = false;
    uvm_component* comp   = NULL;
    sc_simcontext* simc_p = sc_get_curr_simcontext();
    sc_object*     obj    = simc_p->first_object();

    uvmsc_boost::smatch what;
    uvmsc_boost::regex  re(name);

    obj = simc_p->first_object();
    while ((obj != NULL) && (bfound == false))
    {
        comp = DCAST<uvm_component*>(obj);
        if ((comp != NULL) &&
                uvmsc_boost::regex_match((const std::string) obj->name(), what, re))
        {
            bfound = true;
        }
        obj = simc_p->next_object();
    }
    return comp;
}

//------------------------------------------------------------------------------
// Function: find_module
// 
// Regular expression search for OVM components base on type name.  Returns
// the first match.
//------------------------------------------------------------------------------
uvm_component* uvm_manager::find_module(const char* name) {
  bool           bfound = false;
  uvm_component* comp   = NULL;
  sc_simcontext* simc_p = sc_get_curr_simcontext();
  sc_object*     obj    = simc_p->first_object();

  uvmsc_boost::smatch what;
  uvmsc_boost::regex  re(name);
  
  while ((obj != NULL) && (bfound == false))
  {
    comp = DCAST<uvm_component*>(obj);
    if ((comp != NULL) &&
        uvmsc_boost::regex_match(comp->get_type_name(), what, re))
    {
        bfound = true;
    }
    obj = simc_p->next_object();
  }
  return comp;

}

//------------------------------------------------------------------------------
// Function: find_all
// 
// Regular expression search for OVM components base on instance name.  Returns
// a vector of all components that match the search criteria.  Default is to
// return all components.
//------------------------------------------------------------------------------
std::vector<uvm_component*> uvm_manager::find_all(const char* name) {
  std::vector<uvm_component*> comp_vector;
  uvm_component* comp   = NULL;
  sc_simcontext* simc_p = sc_get_curr_simcontext();
  sc_object*     obj    = simc_p->first_object();

  uvmsc_boost::smatch what;
  uvmsc_boost::regex  re(name);
  
  while (obj != NULL)
  {
    comp = DCAST<uvm_component*>(obj);
    if ((comp != NULL) &&
        uvmsc_boost::regex_match((const std::string) obj->name(), what, re))
    {
        comp_vector.push_back(comp);
    }
    obj = simc_p->next_object();
  }
  return comp_vector;

}

//------------------------------------------------------------------------------
// Function: find_all_module
// 
// Regular expression search for OVM components base on type name.  Returns
// a vector of all components that match the search criteria.
//------------------------------------------------------------------------------
std::vector<uvm_component*> uvm_manager::find_all_module(const char* name) {
  std::vector<uvm_component*> comp_vector;
  uvm_component* comp   = NULL;
  sc_simcontext* simc_p = sc_get_curr_simcontext();
  sc_object*     obj    = simc_p->first_object();

  uvmsc_boost::smatch what;
  uvmsc_boost::regex  re(name);
  
  while (obj != NULL)
  {
    comp = DCAST<uvm_component*>(obj);
    if ((comp != NULL) &&
        uvmsc_boost::regex_match(comp->get_type_name(), what, re))
    {
        comp_vector.push_back(comp);
    }
    obj = simc_p->next_object();
  }
  return comp_vector;

}

void uvm_manager::set_stop_mode(stop_mode_enum mode) {
  m_stop_mode = mode;
}

void uvm_manager::set_global_timeout(sc_time t) {
  m_global_timeout = t;
}

void uvm_manager::set_global_stop_timeout(sc_time t) {
  m_stop_timeout = t;
}

void uvm_manager::wait_for_global_timeout() {
  
  sc_time tdur = m_global_timeout - sc_time_stamp();

  wait(tdur);

  // global timeout has expired => run phase has ended

  end_run_phase();
}

void uvm_manager::stop_request() {

  sc_spawn_options o;

  MARK_THREAD_INVISIBLE(o);

  // first spawn thread that will wait for m_stop_timeout to expire
  sc_spawn(sc_bind(&uvm_manager::wait_for_stop_timeout, this),
           "uvm_wait_for_stop_timeout",
            &o
  );

  // spawn helper process that will spawn all the stop tasks
  // and wait for spawned hierarchy to terminate
 
  sc_spawn(sc_bind(&uvm_manager::stop_spawner, this),
           "uvm_stop_spawner",
           &o
  );
}

void uvm_manager::wait_for_stop_timeout() {

  sc_time tdur = m_stop_timeout - sc_time_stamp();

  wait(tdur);

  // stop timeout has expired => run phase has ended
  end_run_phase();

}

void uvm_manager::stop_spawner() {

  // find all top-level modules and spawn stop on each top module hierarchy

  const std::vector<sc_object*>& tops = sc_get_top_level_objects();
  for (unsigned i = 0; i < tops.size(); i++) {
    sc_object* top = tops[i];
    sc_module* top_mod = DCAST<sc_module*>(top);
    if (top_mod) {
      spawn_stop(top_mod);
    }
  }

  // wait for all stop processes to terminate

  if (m_join_stop.process_count() > 0) {
    m_join_stop.wait();
  }

  // all stop tasks have returned => 
  // 1. call kill() on all uvm_components 
  // 2. end run phase

  do_kill_all();
  end_run_phase();
}

void uvm_manager::spawn_stop(sc_module* mod) {

  sc_simcontext* context = sc_get_curr_simcontext();

  // spawn mod::stop() if mod is an uvm_component, and
  // it overrode enable_stop_interrupt() to return true;
  // spawn mod::stop() as a child of mod

  uvm_component* comp = DCAST<uvm_component*>(mod);
  if (comp && comp->enable_stop_interrupt()) {

    // check if this component already has a child called "stop"

    std::string nm = std::string(mod->name()) + std::string(".stop");
    if (sc_find_object(nm.c_str())) {
      char msg[1048];
      sprintf(msg, "\nuvm_component is %s", mod->name()); 
      SC_REPORT_ERROR(UVM_MULTIPLE_STOP_PROCS_, msg);
    }

    sc_process_b* proc = sc_get_current_process_b();
    context->hierarchy_push(mod);
    RESET_PROC_EXTERN(proc);
    sc_process_handle stop_handle = 
      sc_spawn(sc_bind(&uvm_component::stop, comp), "stop");
    context->hierarchy_pop();
    SET_PROC_EXTERN(proc);
    m_join_stop.add_process(stop_handle);
  }

  // recurse over children

  const std::vector<sc_object*>& children = mod->get_child_objects();
  for (unsigned i = 0; i < children.size(); i++) {
    sc_object* child = children[i];
    sc_module* mod_child = DCAST<sc_module*>(child);
    if (mod_child) {
      spawn_stop(mod_child);
    }
  }
}

void uvm_manager::end_run_phase() {

  static bool invoked = false; 

  if (!invoked) {
    invoked = true;
  } else {
    // end_run_phase() has already been called;
    // this can happen if uvm_stop_request has been called 
    // but the stop processes do not all return; then global_timeout and
    // stop_timeout will expire at same time, and both will call 
    // end_run_phase() 
    return;
  }

  // do the post-run phases

  do_extract_all();
  do_check_all();
  do_report_all();

  // call sc_stop() if m_stop_mode is set appropriately 

  if (m_stop_mode == UVM_SC_STOP) {
    sc_stop();
  }
  
}

void uvm_manager::do_kill_all() {

  // find all top-level modules and call kill on each top module hierarchy

  const std::vector<sc_object*>& tops = sc_get_top_level_objects();
  for (unsigned i = 0; i < tops.size(); i++) {
    sc_object* top = tops[i];
    sc_module* top_mod = DCAST<sc_module*>(top);
    if (top_mod) {
      do_kill(top_mod);
    }
  }
}

void uvm_manager::do_kill(sc_module* mod) {

  // call mod::kill() if mod is an uvm_component

  uvm_component* comp = DCAST<uvm_component*>(mod);
  if (comp) {
    comp->kill();
  }

  // recurse over children

  const std::vector<sc_object*>& children = mod->get_child_objects();
  for (unsigned i = 0; i < children.size(); i++) {
    sc_object* child = children[i];
    sc_module* mod_child = DCAST<sc_module*>(child);
    if (mod_child) {
      do_kill(mod_child);
    }
  }
}

void uvm_manager::do_extract_all() {

  // find all top-level modules and call extract on each top module hierarchy

  const std::vector<sc_object*>& tops = sc_get_top_level_objects();
  for (unsigned i = 0; i < tops.size(); i++) {
    sc_object* top = tops[i];
    sc_module* top_mod = DCAST<sc_module*>(top);
    if (top_mod) {
      do_extract(top_mod);
    }
  }
}

void uvm_manager::do_extract(sc_module* mod) {

  // call mod::extract() if mod is an uvm_component

  uvm_component* comp = DCAST<uvm_component*>(mod);
  if (comp) {
    comp->extract();
  }

  // recurse over children

  const std::vector<sc_object*>& children = mod->get_child_objects();
  for (unsigned i = 0; i < children.size(); i++) {
    sc_object* child = children[i];
    sc_module* mod_child = DCAST<sc_module*>(child);
    if (mod_child) {
      do_extract(mod_child);
    }
  }
}

void uvm_manager::do_check_all() {

  // find all top-level modules and call check on each top module hierarchy

  const std::vector<sc_object*>& tops = sc_get_top_level_objects();
  for (unsigned i = 0; i < tops.size(); i++) {
    sc_object* top = tops[i];
    sc_module* top_mod = DCAST<sc_module*>(top);
    if (top_mod) {
      do_check(top_mod);
    }
  }
}

void uvm_manager::do_check(sc_module* mod) {

  // call mod::check() if mod is an uvm_component

  uvm_component* comp = DCAST<uvm_component*>(mod);
  if (comp) {
    comp->check();
  }

  // recurse over children

  const std::vector<sc_object*>& children = mod->get_child_objects();
  for (unsigned i = 0; i < children.size(); i++) {
    sc_object* child = children[i];
    sc_module* mod_child = DCAST<sc_module*>(child);
    if (mod_child) {
      do_check(mod_child);
    }
  }
}

void uvm_manager::do_report_all() {

  // find all top-level modules and call report on each top module hierarchy

  const std::vector<sc_object*>& tops = sc_get_top_level_objects();
  for (unsigned i = 0; i < tops.size(); i++) {
    sc_object* top = tops[i];
    sc_module* top_mod = DCAST<sc_module*>(top);
    if (top_mod) {
      do_report(top_mod);
    }
  }
}

void uvm_manager::do_report(sc_module* mod) {

  // call mod::report() if mod is an uvm_component

  uvm_component* comp = DCAST<uvm_component*>(mod);
  if (comp) {
    comp->report();
  }

  // recurse over children

  const std::vector<sc_object*>& children = mod->get_child_objects();
  for (unsigned i = 0; i < children.size(); i++) {
    sc_object* child = children[i];
    sc_module* mod_child = DCAST<sc_module*>(child);
    if (mod_child) {
      do_report(mod_child);
    }
  }
}

void uvm_manager::set_top(sc_core::sc_module *comp)
{
  m_tops.push_back(comp);
}

std::vector<uvm_component*> uvm_manager::get_uvm_component_tops()
{
  std::vector<uvm_component*> tops;
  uvm_component * pcomp;

  for (int i = 0; i < m_tops.size(); i++)
  {
    pcomp = DCAST<uvm_component*>(m_tops[i]);
    if (pcomp != NULL)
        tops.push_back(pcomp);
  }

  return tops;
}

std::vector<sc_core::sc_module*> uvm_manager::get_tops()
{
  return m_tops;
}

unsigned int uvm_manager::get_num_tops()
{
  return m_tops.size();
}


//////////

} // namespace uvm

