//----------------------------------------------------------------------
//   Copyright 2009 Cadence Design Systems, Inc.
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

/*! \file uvm_factory.cpp
  \brief Factory for UVM-SC objects.
*/

#include "base/uvm_factory.h"
#include "base/uvm_config_db.h"

#include "sysc/utils/sc_hash.h"
#include "sysc/utils/sc_iostream.h"
#include "string.h"

using namespace std;
using namespace sc_core;

namespace uvm {

string INST_OVERRIDE_CNTXT = "uvm_factory_inst_override";

//------------------------------------------------------------------------------
//
// uvm_creator
// uvm_object_creator
// uvm_component_creator
// uvm_factory
//
//------------------------------------------------------------------------------


///////////

//------------------------------------------------------------------------------
// uvm_creator implementation 
//------------------------------------------------------------------------------

uvm_creator::uvm_creator() { }

uvm_creator::~uvm_creator() { }

uvm_object_creator* uvm_creator::as_object_creator() { return 0; }

uvm_component_creator* uvm_creator::as_component_creator() { return 0; }

///////////

//------------------------------------------------------------------------------
// uvm_object_creator implementation 
//------------------------------------------------------------------------------

uvm_object_creator::uvm_object_creator() { }

uvm_object_creator::~uvm_object_creator() { }

uvm_object_creator* uvm_object_creator::as_object_creator() { 
  return this; 
}

///////////

//------------------------------------------------------------------------------
// uvm_component_creator implementation 
//------------------------------------------------------------------------------

uvm_component_creator::uvm_component_creator() { }

uvm_component_creator::~uvm_component_creator() { }

uvm_component_creator* uvm_component_creator::as_component_creator() { 
  return this; 
}

///////////

//------------------------------------------------------------------------------
//
// CLASS: uvm_factory_rep
//
// Internal implementation class.
// uvm_factory delegetates to this class to do the real work.
//
//---------------------------------------------------------------------------

/*! \class uvm_factory_rep
  \brief uvm_factory delegetates to this class to do the real work.

  
*/
class uvm_factory_rep {
public:
  uvm_factory_rep();
  ~uvm_factory_rep();
  //
  int register_class_creator(
    const string & type_name, 
    uvm_creator* creator
  );
  int register_component_creator(
    const string & type_name,
    uvm_component_creator* creator
  );
  //
  uvm_object* create_uvm_object(
    string type_name,
    string inst_path = "",
    string name = "",
    bool no_overrides = false
  );
  uvm_component* create_component(
    string type_name,
    string inst_path = "",
    string name = ""
  );
  void* create_registered_class(
    const std::string & type_name
  );
  //
  void set_type_override(
    string original_type_name,
    string replacement_type_name,
    bool replace
  );
  void set_inst_override(
    string inst_path,
    string original_type_name,
    string replacement_type_name
  );
  //
  string get_type_override(string type_name);
  string get_inst_override(string type_name, string inst_path);
  string get_override(string type_name, string inst_path);
  void print_all_overrides(); // for debugging use
  void print_registered_types();
  void print_type_overrides();
  void print_inst_overrides();
  //
  bool is_component_registered(const string & type_name);
  bool is_uvm_object_registered(const string & type_name);
  bool is_class_registered(const string & type_name);
protected:
  sc_strhash<uvm_creator*> creator_map;
  sc_strhash<string*> type_overrides;
};

//------------------------------------------------------------------------------
// uvm_factory_rep implementation 
//------------------------------------------------------------------------------

uvm_factory_rep::uvm_factory_rep() {
}

uvm_factory_rep::~uvm_factory_rep() {
}

int uvm_factory_rep::register_class_creator(
  const string & type_name,
  uvm_creator* creator
) { 
  creator_map.insert(strdup(type_name.c_str()), creator);
  return 1;
}

// return NULL if object cannot be created

uvm_object* uvm_factory_rep::create_uvm_object(
  string type_name,
  string inst_path,
  string name,
  bool no_overrides
) { 
  string typ;
  if (no_overrides) {
    typ = type_name;
  } else {
    string path = inst_path;
    if (name != "") {
      path = path + string(".") + name;
    }
    typ = get_override(type_name,path);
  }
  uvm_creator* c = creator_map[typ.c_str()];  
  if (!c) { 
    char msg[1024];
    sprintf(msg," Type = %s",typ.c_str());
    SC_REPORT_WARNING(UVM_CREATOR_NOT_FOUND_,msg);
    return 0; 
  }
  uvm_object_creator* cobj = c->as_object_creator();
  if (!cobj) { 
    char msg[1024];
    sprintf(msg," Type = %s",typ.c_str());
    SC_REPORT_WARNING(UVM_CREATOR_NOT_OBJECT_,msg);
    return 0; 
  }
  uvm_object* obj = cobj->create(name);
  return obj;
}

string uvm_factory_rep::get_type_override(string type_name) {
  string* t = type_overrides[type_name.c_str()];
  if (!t) return "";
  return *t;
}

string uvm_factory_rep::get_inst_override(string type_name, string inst_path) {
  string typ = "";

  uvm_config_db<string>::get(INST_OVERRIDE_CNTXT, inst_path, type_name, typ);
  return typ;
}

string uvm_factory_rep::get_override(string type_name, string inst_path) {
  string typ = "";
  typ = get_inst_override(type_name,inst_path);
  if (typ.length()) {
    return typ;
  }
  typ = get_type_override(type_name);
  if (typ.length()) {
    return typ;
  }
  return type_name;
}

// return NULL if component cannot be created

uvm_component* uvm_factory_rep::create_component(
  string type_name,
  string inst_path,
  string name
) { 
  string path = inst_path + string(".") + name;
  string typ = get_override(type_name,path);
  uvm_creator* c = creator_map[typ.c_str()];  
  if (!c) { 
    char msg[1024];
    sprintf(msg," Type = %s",typ.c_str());
    SC_REPORT_WARNING(UVM_CREATOR_NOT_FOUND_,msg);
    return 0; 
  }
  uvm_component_creator* ccomp = c->as_component_creator();
  if (!ccomp) { 
    char msg[1024];
    sprintf(msg," Type = %s",typ.c_str());
    SC_REPORT_WARNING(UVM_CREATOR_NOT_COMP_,msg);
    return 0; 
  }
  uvm_component* comp = ccomp->create(name);
  return comp;
}

// if replacement type has not been registered with factory,
// then error out.
// if "replace" is false, and override already exists for 
// "original_type_name", then error out

void uvm_factory_rep::set_type_override(
  string original_type_name,
  string replacement_type_name,
  bool replace
) {
  // check replace_ment_type_name is registered
  if (!creator_map[(char*)(replacement_type_name.c_str())]) {
    char msg[1024];
    sprintf(msg,
      " Problem with replacement type in set_type_override. Type = %s",
      replacement_type_name.c_str()
    );
    SC_REPORT_ERROR(UVM_CREATOR_NOT_FOUND_,msg);
    return; 
  }
  if (!replace && type_overrides[(char*)(original_type_name.c_str())]) {
    char msg[1024];
    sprintf(msg," Type = %s", original_type_name.c_str());
    SC_REPORT_ERROR(UVM_OVERRIDE_EXISTS_,msg);
    return;
  }
  type_overrides.insert(
    strdup(original_type_name.c_str()), 
    new string(replacement_type_name)
  );
}

// if replacement type has not been registered with factory,
// then error out.

void uvm_factory_rep::set_inst_override(
  string inst_path,
  string original_type_name,
  string replacement_type_name
) {
  // check replace_ment_type_name is registered
  if (!creator_map[(char*)(replacement_type_name.c_str())]) {
    char msg[1024];
    sprintf(msg,
      " Problem with replacement type in set_inst_override. Type = %s",
      replacement_type_name.c_str()
    );
    SC_REPORT_ERROR(UVM_CREATOR_NOT_FOUND_,msg);
    return; 
  }

  uvm_config_db<string>::set(INST_OVERRIDE_CNTXT, inst_path, original_type_name, replacement_type_name);
}
 
void uvm_factory_rep::print_all_overrides() {
  print_registered_types();
  print_type_overrides();
  print_inst_overrides();
}

void* uvm_factory_rep::create_registered_class(
  const string & type_name
) { 
  uvm_creator* c = creator_map[type_name.c_str()];  
  if (!c) { 
    char msg[1024];
    sprintf(msg," Type = %s",type_name.c_str());
    SC_REPORT_WARNING(UVM_CREATOR_NOT_FOUND_,msg);
    return 0; 
  }
  void* obj = c->create_class(type_name);
  return obj;
}

void uvm_factory_rep::print_registered_types() {
  cerr << "UVM_FACTORY REGISTERED TYPES:" << endl;
  sc_strhash_iter<uvm_creator*> iter(creator_map);
  while (!iter.empty()) {
    const char* c = iter.key();
    cerr << c << endl;
    iter++;
  }
  cerr << endl << endl;
}

void uvm_factory_rep::print_type_overrides() {
  cerr << "UVM_FACTORY REGISTERED TYPES:" << endl;
  sc_strhash_iter<string*> iter(type_overrides);
  while (!iter.empty()) {
    const char* orig = iter.key();
    string* repl = iter.contents();
    cerr << orig << " --> " << *repl << endl;
    iter++;
  }
  cerr << endl << endl;
}

void uvm_factory_rep::print_inst_overrides() {
// TODO:
/*
  cerr << "UVM_FACTORY INST OVERRIDES:" << endl;
  for (unsigned i = 0; i < inst_overrides.m_vec.size(); i++) {
    uvm_config_item* item = inst_overrides.m_vec[i];
    uvm_config_item_string* item_s = item->as_string();
    cerr << item_s->m_instname << " " << item_s->m_field 
      << " --> " << item_s->value() << endl; 
  }
*/
}

bool uvm_factory_rep::is_class_registered(const string & type_name) {
  uvm_creator* c = creator_map[type_name.c_str()];
  if (c) {
    return true;
  }
  return false;
}

bool uvm_factory_rep::is_component_registered(const string & type_name) {
  uvm_creator* c = creator_map[type_name.c_str()];
  if (c) {
    uvm_component_creator* ccomp = c->as_component_creator();
    if (ccomp) return true;
  }
  return false;
}

bool uvm_factory_rep::is_uvm_object_registered(const string & type_name) {
  uvm_creator* c = creator_map[type_name.c_str()];
  if (c) {
    uvm_object_creator* cobj = c->as_object_creator();
    if (cobj) return true;
  }
  return false;
}

///////////

//------------------------------------------------------------------------------
// uvm_factory implementation
//------------------------------------------------------------------------------

uvm_factory_rep* uvm_factory::m_rep = 0;

int uvm_factory::register_class_creator(
  const string & type_name,
  uvm_creator* creator
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  int r = m_rep->register_class_creator(
    type_name,
    creator
  );
  return r;
}

int uvm_factory::register_uvm_object_creator(
  const string & type_name,
  uvm_object_creator* creator
) {
  return register_class_creator(type_name, creator);
}

int uvm_factory::register_component_creator(
  const string & type_name,
  uvm_component_creator* creator
) {
  return register_class_creator(type_name, creator);
}

uvm_object* uvm_factory::create_uvm_object(
  string type_name,
  string inst_path,
  string name,
  bool no_overrides
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  uvm_object* obj = m_rep->create_uvm_object(
    type_name,
    inst_path,
    name,
    no_overrides
  );
  return obj;
}

uvm_component* uvm_factory::create_component(
  string type_name,
  string inst_path,
  string name
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  uvm_component* comp = m_rep->create_component(
    type_name,
    inst_path,
    name
  );
  return comp;
}

void* uvm_factory::create_registered_class(const std::string & type_name)
{
  if (!m_rep) m_rep = new uvm_factory_rep();
  return m_rep->create_registered_class(type_name);
}

void uvm_factory::set_type_override(
   string original_type_name,
   string replacement_type_name,
   bool replace
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  m_rep->set_type_override(
    original_type_name,
    replacement_type_name,
    replace
  );
}

void uvm_factory::set_inst_override(
   string inst_path,
   string original_type_name,
   string replacement_type_name
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  m_rep->set_inst_override(
    inst_path,
    original_type_name,
    replacement_type_name
  );
}
 
string uvm_factory::get_type_override(
   string original_type_name
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  return m_rep->get_type_override(original_type_name);
}

string uvm_factory::get_inst_override(
   string original_type_name,
   string inst_path
) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  return m_rep->get_inst_override(original_type_name, inst_path);
}

void uvm_factory::print_all_overrides() {
  if (!m_rep) m_rep = new uvm_factory_rep();
  m_rep->print_all_overrides();
}

bool uvm_factory::is_component_registered(const string & type_name) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  return m_rep->is_component_registered(type_name);
}

bool uvm_factory::is_uvm_object_registered(const string & type_name) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  return m_rep->is_uvm_object_registered(type_name);
}

bool uvm_factory::is_class_registered(const string & type_name) {
  if (!m_rep) m_rep = new uvm_factory_rep();
  return m_rep->is_class_registered(type_name);
}

///////////

//------------------------------------------------------------------------------
// implementation of global functions to create uvm_object/uvm_component,
// and to set up overrides.
//------------------------------------------------------------------------------

uvm_object* uvm_create_object(
  std::string type_name,
  std::string inst_path,
  std::string name,
  bool no_overrides 
) {
  return uvm_factory::create_uvm_object(type_name, inst_path, name, no_overrides);
}

uvm_component* uvm_create_component(
  std::string type_name,
  std::string inst_path,
  std::string name
) {
  return uvm_factory::create_component(type_name, inst_path, name);
}

void uvm_set_type_override(
  std::string original_type_name,
  std::string replacement_type_name,
  bool replace 
) {
  uvm_factory::set_type_override(
    original_type_name, replacement_type_name, replace
  );
}

void uvm_set_inst_override(
  std::string inst_path,
  std::string original_type_name,
  std::string replacement_type_name
) {
  uvm_factory::set_inst_override(
    inst_path, original_type_name, replacement_type_name
  );
}


///////////


} // namespace uvm
