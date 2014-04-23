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

/*! \file uvm_ml_hierarchy.h
  \brief Header file for ML hierarchy.
*/
#ifndef UVM_ML_HIERARCHY_H
#define UVM_ML_HIERARCHY_H

#include "systemc.h"
#ifdef NC_SYSTEMC
#include "sysc/utils/sc_iostream.h"
#else
#include "sysc/kernel/sc_simcontext.h"
#endif
#include <typeinfo>
#include <stdio.h>
#include <map>

#include "uvm_ml_adapter_imp_spec_macros.h"
#include "uvm_ml_adapter_imp_spec_headers.h"
#include "uvm.h"

using namespace std;
using namespace uvm;

namespace uvm_ml {

class parent_component_proxy;

/*! \class uvm_ml_proxy_helper
  \brief helper class for creating the proxy hierarchy.

  
*/

class uvm_ml_special_component: public uvm_component
{
public:
  uvm_ml_special_component(const sc_module_name & name): uvm_component(name) {}
  virtual ~uvm_ml_special_component() {}
};

class uvm_ml_proxy_helper: public uvm_ml_special_component 
{
public:
  uvm_ml_proxy_helper(const sc_module_name & name);
  uvm_ml_proxy_helper(const sc_module_name & name, const string & remaining_path);
  virtual ~uvm_ml_proxy_helper() {};

  parent_component_proxy * get_proxy() { return m_proxy; }

  virtual bool is_true_component() { return false; }

  UVM_COMPONENT_UTILS(uvm_ml_proxy_helper)
private:
  parent_component_proxy * m_proxy;
};
UVM_COMPONENT_REGISTER( uvm_ml_proxy_helper)

/*! \struct child_subtree_registry_class
  \brief Maintain the attributes of the child sub-tree.

  
*/
struct child_subtree_registry_class {
  uvm_component *          child_junction_node;
  vector <uvm_component *> descendants;
};

/*! \class parent_component_proxy
  \brief Parent proxy.

  
*/
class parent_component_proxy: public uvm_ml_special_component {
private:

  int                   m_proxy_id;
  int                   m_parent_framework_id;

public:
  parent_component_proxy(const sc_module_name & nm);

  virtual ~parent_component_proxy() {};

  UVM_COMPONENT_UTILS(parent_component_proxy)

    static parent_component_proxy * create(const string & parent_full_name,
                                           int            parent_framework_id,
                                           int            parent_junction_node_id);

  int Id() { return m_proxy_id; }
  void SetId(int id) { m_proxy_id = id; }

  int ParentFrameworkId() { return m_parent_framework_id; }
  void SetParentFrameworkId(int id) { m_parent_framework_id = id; }

  int  add_node(const char * child_type_name, 
                const char * child_instance_name);

/*! \class FullNameComparer
  \brief Compare full name of parent proxy.

  
*/
  class FullNameComparer
  {
  private:
      string x;
  public:
      FullNameComparer(const string & s){ x = s; }
      ~FullNameComparer() {};
      string X() { return x; }
      bool operator ()(parent_component_proxy *arg) { return arg->name() == X(); }
  };
  virtual bool is_true_component() { return false; }
};
UVM_COMPONENT_REGISTER(parent_component_proxy)

class child_component_proxy: public uvm_ml_special_component {
private:
  string       m_component_type_name;
  string       m_instance_name;
  string       m_parent_name;
  string       m_target_frmw_ind;
  int          m_child_junction_node_id;
  int          m_parent_id;
public:
  child_component_proxy(sc_module_name);

  virtual ~child_component_proxy() {};
  void phase_started(uvm_phase *phase);
  void phase_ready_to_end(uvm_phase *phase);
  void phase_ended(uvm_phase *phase);
  void build_phase(uvm_phase *phase);
  void connect_phase(uvm_phase *phase);
  void end_of_elaboration_phase(uvm_phase *phase);
  void start_of_simulation_phase(uvm_phase *phase);
  void extract_phase(uvm_phase *phase);
  void check_phase(uvm_phase *phase);
  void report_phase(uvm_phase *phase);
  void final_phase(uvm_phase *phase);

  UVM_COMPONENT_UTILS(child_component_proxy)

};
UVM_COMPONENT_REGISTER(child_component_proxy)

}
#endif
