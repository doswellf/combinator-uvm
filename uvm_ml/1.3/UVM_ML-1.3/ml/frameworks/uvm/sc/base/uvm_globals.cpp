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

/*! \file uvm_globals.cpp
  \brief Implementation of global UVM-SC functionality.
*/

#include "systemc.h"
#include <packages/boost/include/regex.hpp>

#include "base/uvm_globals.h"
#include "base/uvm_component.h"
#include "base/uvm_manager.h"
#include "base/uvm_config_db.h"

using namespace sc_core;


namespace uvm {

static std::vector<uvm_component *> uvm_rsrc_callback_vec;
static std::vector<uvm::uvm_component *> * uvm_config_callback_vec = NULL;

//------------------------------------------------------------------------------
//
// Implementation of some of the global UVM functions.
//
// Delegates to the internal class uvm_manager to do the real work.
//
//------------------------------------------------------------------------------

uvm_component* uvm_find_component(const char* name) {
  return get_uvm_manager()->find_component(name); 
}

void uvm_set_stop_mode(stop_mode_enum mode) {
  get_uvm_manager()->set_stop_mode(mode); 
}

void uvm_set_global_timeout(sc_time t) {
  get_uvm_manager()->set_global_timeout(t); 
}

void uvm_set_global_stop_timeout(sc_time t) {
  get_uvm_manager()->set_global_stop_timeout(t); 
}

void uvm_stop_request() {
  get_uvm_manager()->stop_request(); 
}

/*
static uvm_pool<uvm_event> *p_global_event_pool = 0;

uvm_pool<uvm_event> *get_global_event_pool()
{
  if (p_global_event_pool)
    return p_global_event_pool;
  else
    p_global_event_pool = new uvm_pool<uvm_event>("global_event_pool");
}
*/

std::vector<sc_core::sc_module*> uvm_get_tops() {
  return get_uvm_manager()->get_tops();
}

std::vector<uvm_component*> uvm_get_uvm_component_tops() {
  return get_uvm_manager()->get_uvm_component_tops();
}

std::vector<sc_core::sc_module*> uvm_get_children (sc_core::sc_module * pmod) {
  std::vector<sc_object*> child_obj_vec;
  std::vector<sc_core::sc_module*> child_mod_vec;
  sc_core::sc_module *pchild;

  child_obj_vec = pmod->get_child_objects();

  for (int i = 0; i < child_obj_vec.size(); i++)
  {
    pchild = DCAST<sc_core::sc_module*>(child_obj_vec[i]);
    if (pchild != NULL)
      child_mod_vec.push_back(pchild);
  }
  return child_mod_vec;

}

//----------------------------------------------------------------------
//! Return the hierachical path (context) of the component
/*!
 *  @return Hierachical path of the component.
 */
std::string uvm_get_cntxt_name(uvm_component *comp)
{
    return comp->name();

}

//----------------------------------------------------------------------
//! Convert a glob expression to regular expression.
/*!
 *  @param glob - string in glob format
 *
 *  @return string in regular expression format.
 */
std::string uvm_glob_to_regex(const std::string &glob)
{
    uvmsc_boost::regex re("(\\*)|(\\?)|([[:blank:]])|(\\.|\\+|\\^|\\$|\\[|\\]|\\(|\\)|\\{|\\}|\\\\)");
    //const char*        format = "(?1\\\\w+)(?2\\.)(?3\\\\s*)(?4\\\\$&)";
    //const char*        format = "(?1\\\.*)(?2\\.)(?3\\\\s*)(?4\\\\$&)";
    const char*        format = "(?1\\.*)(?2\\.)(?3\\\\s*)(?4\\\\$&)";
    //const char*        format = "(?1\\\\.*)(?2\\.)(?3\\\\s*)(?4\\\\$&)";
    std::stringstream  final;
    int                length;

    length = glob.length();
    if (length == 0)
    {
        final << "/0";
    }
    // already a regular expression
    else if ((glob.substr(0, 1).compare(uvm_regex_encap) == 0) && 
             (glob.substr(length - 1, 1).compare(uvm_regex_encap) == 0))
    {
        final << glob;
    }
    else
    {
        //final << uvm_regex_encap;
        std::ostream_iterator<char, char> oi(final);
        uvmsc_boost::regex_replace(oi, glob.begin(), glob.end(), re, format, uvmsc_boost::match_default | uvmsc_boost::format_all);
        //final << uvm_regex_encap;
    }

    return final.str();
}

void uvm_set_config_string(
  const std::string& instname,
  const std::string& field,
  const std::string& val
)
{
  uvm_config_db<std::string>::set(0, instname, field, val);
}

void uvm_set_config_object(
  const std::string& instname,
  const std::string& field,
  uvm_object* val,
  bool clone
)
{
  // TODO: clone
  uvm_config_db<uvm_object *>::set(0, instname, field, val);
}

void uvm_register_config_callback(uvm_component *comp)
{
    if (uvm_config_callback_vec == NULL)
        uvm_config_callback_vec = new std::vector<uvm::uvm_component *>;

    uvm_config_callback_vec->push_back(comp);
}

void uvm_unregister_config_callback(uvm_component *comp)
{
    if (uvm_config_callback_vec == NULL)
        cout << "ERROR: uvm_unregister_config_callback - vector is empty" << endl;

    uvm_config_callback_vec->erase( std::remove( uvm_config_callback_vec->begin(), uvm_config_callback_vec->end(), comp ), uvm_config_callback_vec->end() ); 

    if (uvm_config_callback_vec->size() == 0)
        delete uvm_config_callback_vec;

}

void uvm_config_callback(std::string cntxt, std::string inst_name, std::string field_name, uvm_resource_base * rsrc)
{

    for (int i = 0; i < uvm_config_callback_vec->size(); i++)
    {
        (*uvm_config_callback_vec)[i]->config_callback(cntxt, inst_name, field_name, rsrc);
    }
}

void uvm_register_rsrc_callback(uvm_component *comp)
{
    uvm_rsrc_callback_vec.push_back(comp);
}

void uvm_rsrc_callback(uvm_rsrc_action action, std::string scope, std::string name, uvm_resource_base * rsrc)
{
    for (int i = 0; i < uvm_rsrc_callback_vec.size(); i++)
    {
        uvm_rsrc_callback_vec[i]->rsrc_callback(action, scope, name, rsrc);
    }
}


} // namespace uvm

