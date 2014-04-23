#include "uvm_ml_adapter_imp_spec_headers.h"
#include "uvm_ml_adapter_imp_spec_macros.h"
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

/*! \file uvm_ml_hierarchy.cpp
  \brief Implementation of ML hierarchy.
*/
#include <algorithm>
#include "uvm_ml_adapter.h"
#include "uvm_ml_hierarchy.h"

using namespace std;
using namespace uvm;

namespace uvm_ml {

parent_component_proxy::parent_component_proxy(const sc_module_name & nm): uvm_ml_special_component(nm) {
}

parent_component_proxy * parent_component_proxy::create(const string & parent_full_name, // Static method
                                                        int            parent_framework_id,
                                                        int            parent_junction_node_id) {

    parent_component_proxy * ret = NULL;
    uvm_component * context_component = NULL;

    size_t first_dot = parent_full_name.find(".");
    if(first_dot == string::npos) {
        // Parent full name is simple, no dots
        ret =  new parent_component_proxy(sc_module_name(parent_full_name.c_str()));
    }
    else {
        // Need to build auxiliary dummy hierarchy in order to work around the fact 
        // that the instance name cannot be dotted
        ret = uvm_ml_utils::create_parent_proxy_with_helpers(NULL, parent_full_name);
    }
    if (context_component != NULL)
        sc_core::sc_get_curr_simcontext()->hierarchy_pop();

    if (ret != NULL)
      uvm_ml_utils::add_parent_proxy(ret, parent_framework_id, parent_junction_node_id);

    return ret;
}

int parent_component_proxy::add_node(const char * child_type_name, 
                                     const char * child_instance_name) {
    int node_id = -1;

    simcontext()->hierarchy_push( this );
    uvm_component * comp = uvm_factory::create_component(child_type_name, name(), child_instance_name);
    simcontext()->hierarchy_pop();
    if (comp) {
      node_id = uvm_ml_utils::add_quasi_static_tree_node(comp);
    }
    return node_id;
}

/////////////////////////////

uvm_ml_proxy_helper::uvm_ml_proxy_helper(const sc_module_name & name): uvm_ml_special_component(name) {
}

uvm_ml_proxy_helper::uvm_ml_proxy_helper(const sc_module_name & nm, const string & remaining_path): uvm_ml_special_component(nm) {
  size_t dot_pos = remaining_path.find(".");

  if (dot_pos == string::npos) {
    m_proxy = new parent_component_proxy(sc_module_name(remaining_path.c_str()));
    // Save it because the helper may be later deleted
  } else {
    string next_instance_name = remaining_path.substr(0, dot_pos);
    string next_remaining_path = remaining_path.substr(dot_pos + 1);
    uvm_ml_proxy_helper * child_helper = 
      new uvm_ml_proxy_helper(sc_module_name(next_instance_name.c_str()), next_remaining_path);
    m_proxy = child_helper->get_proxy();
  }
}

// Find an existing hierarchical tree for the new parent proxy
// To substitute missing hierarchical instances (belonging to foreign languages) - create dummy helper components
// The latter is done in a recursive manner

parent_component_proxy * uvm_ml_utils::create_parent_proxy_with_helpers(sc_module *    parent_helper,
                                                                        const string & path)
{
  parent_component_proxy * proxy = NULL;

  size_t remaining_path_pos = path.find(".");

  if (remaining_path_pos == string::npos) {
      if (parent_helper)
          sc_core::sc_get_curr_simcontext()->hierarchy_push(parent_helper);
      proxy = new parent_component_proxy(sc_module_name(path.c_str()));
      if (parent_helper)
          sc_core::sc_get_curr_simcontext()->hierarchy_pop();
  } else {
      // The helpers and the proxy must be instantiated recursively in order to build the correct full path
      string instance_name = path.substr(0,remaining_path_pos);
      string full_name;
      if (parent_helper == NULL)
	  full_name = instance_name;
      else {
	  full_name = string(parent_helper->name()) + "." + instance_name;
      }
      string remaining_path = path.substr(remaining_path_pos+1);

      sc_object * old_object = sc_find_object(full_name.c_str());

      if (old_object == NULL) {
          if (parent_helper)
              sc_core::sc_get_curr_simcontext()->hierarchy_push(parent_helper);
          
          uvm_ml_proxy_helper * helper = new uvm_ml_proxy_helper(sc_module_name(instance_name.c_str()), remaining_path);
          if (parent_helper)
              sc_core::sc_get_curr_simcontext()->hierarchy_pop();
          proxy = helper->get_proxy();
      }
      else {
        sc_module * old_module = dynamic_cast<sc_module *>(old_object);
        assert (old_module != NULL);

        proxy = create_parent_proxy_with_helpers(old_module, remaining_path);
      }
  }
  return proxy;
}

//////////////////////

map<int /* parent junction node id */, parent_component_proxy *>  uvm_ml_utils::parent_proxies;

void uvm_ml_utils::add_parent_proxy(parent_component_proxy * proxy,
                                    int                      parent_framework_id,
                                    int                      parent_junction_node_id)
{
    proxy->SetParentFrameworkId(parent_framework_id);
    proxy->SetId(parent_junction_node_id);
    parent_proxies[parent_junction_node_id] = proxy;
}

parent_component_proxy * uvm_ml_utils::find_parent_proxy_by_id(int parent_junction_node_id)
{
    return parent_proxies[parent_junction_node_id];
}

static vector<child_component_proxy *>child_proxies;

child_component_proxy * uvm_ml_create_component(const string &        target_framework_indicator, 
                                                const string &        component_type_name, 
                                                const string &        instance_name,
                                                const uvm_component * parent)
{
    string parent_name;
  
    parent_name = parent->name();

    uvm_set_config_string("*", "uvm_ml_type_name",   component_type_name);
    uvm_set_config_string("*", "uvm_ml_inst_name",   instance_name);
    uvm_set_config_string("*", "uvm_ml_parent_name", parent_name);
    uvm_set_config_string("*", "uvm_ml_frmw_id",     target_framework_indicator);

    child_component_proxy *p = new child_component_proxy(instance_name.c_str());
    child_proxies.push_back(p);

    return p;
}

}
