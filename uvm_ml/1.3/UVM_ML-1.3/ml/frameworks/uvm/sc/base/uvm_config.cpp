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

/*! \file uvm_config.cpp
  \brief Base class for UVM-SC configuration object.
*/

#include "base/uvm_object.h"
#include "base/uvm_config.h"
#include "base/uvm_component.h"

#include <string>

using namespace std;
using namespace sc_core;
using namespace sc_dt;

//////////////

namespace uvm {

//------------------------------------------------------------------------------
//
// Implementation of configuration.
//
//------------------------------------------------------------------------------

//----------------------------------------------------------------------------
//
// FUNCTION: is_match
//
// Match a string "str", with glob string "expr".
//
// expr" is a string which may contain '*' and '?' characters. A '*'
// indicates matching zero or more characters (using a greedy compare),
// ?' indicates matching any single character.
//
// Returns a 1 if "str" matches the expression string and returns
// 0 if it does not match.
//
//----------------------------------------------------------------------------

static bool is_match(string expr, string str) {
  unsigned e, es, s, ss;
  string tmp;
  e  = 0; s  = 0;
  es = 0; ss = 0;

  while (s != str.length() && expr[e] != '*') {
    if ((expr[e] != str[s]) && (expr[e] != '?'))
      return false;
    e++; s++;
  }
  while (s != str.length()) {
    if (expr[e] == '*') {
      e++;
      if (e == expr.length()) {
        return true;
      }
      es = e;
      ss = s+1;
    }
    else if (expr[e] == str[s] || expr[e] == '?') {
      e++;
      s++;
    }
    else {
      e = es;
      s = ss++;
    }
  }
  while (expr[e] == '*')
    e++;
  if(e == expr.length()) {
    return true;
  }
  else {
    return false;
  }
}

//------------------------------------------------------------------------------
// uvm_config_item implementation
//------------------------------------------------------------------------------

uvm_config_item::uvm_config_item(
  const std::string& instname,
  const std::string& field,
  uvm_component* inst_set_by,
  uvm_config_type type 
) {
  m_instname = instname;
  m_field = field;
  m_inst_set_by = inst_set_by;
  m_type = type;
}

uvm_config_item::~uvm_config_item() { }

void uvm_config_item::print_match(
  uvm_component* inst_req,
  std::string instname_req,
  std::string field_req
) const {
  cout << "get_config match. " << endl;
  cout << "Request: Called from: ";
  if (inst_req) { cout << inst_req->name(); } else { cout << "<null-inst>"; }
  cout << ". inst_path: " << instname_req << ". field: " << field_req << endl;
  cout << "Match: inst_path: " << m_instname << ". field: " << m_field << endl;
  cout << "set_config was called from inst: ";
  if (m_inst_set_by) { cout << m_inst_set_by->name(); } else { cout << "<null_inst>"; }
  cout << endl;
}

/////////////

uvm_config_item_int* uvm_config_item::as_int() { return 0; }

uvm_config_item_string* uvm_config_item::as_string() { return 0; }

uvm_config_item_object* uvm_config_item::as_object() { return 0; }

////////////

//------------------------------------------------------------------------------
// uvm_config_item_int implementation
//------------------------------------------------------------------------------

uvm_config_item_int::uvm_config_item_int(
  const std::string& instname,
  const std::string& field,
  uvm_component* inst_set_by,
  sc_lv<4096> val
) : uvm_config_item(instname,field,inst_set_by,uvm_config_type_int) {
  m_val = val;
}

uvm_config_item_int::~uvm_config_item_int() { }

uvm_config_item_int* uvm_config_item_int::as_int() { return this; }

sc_lv<4096> uvm_config_item_int::value() const { return m_val; }

void uvm_config_item_int::print() const {
  cout << "Configuration item lv: " << m_instname << " " << m_field
    << " : from component ";
  if (m_inst_set_by) {
    cout << m_inst_set_by->name() << endl;
  } else {
    cout << "<global>" << endl;
  }
}

////////////

//------------------------------------------------------------------------------
// uvm_config_item_string implementation
//------------------------------------------------------------------------------

uvm_config_item_string::uvm_config_item_string(
  const std::string& instname,
  const std::string& field,
  uvm_component* inst_set_by,
  const std::string& val
) : uvm_config_item(instname,field,inst_set_by,uvm_config_type_string) {
  m_val = val;
}

uvm_config_item_string::~uvm_config_item_string() { }

uvm_config_item_string* uvm_config_item_string::as_string() { return this; }

string uvm_config_item_string::value() const { return m_val; }

void uvm_config_item_string::print() const {
  cout << "Configuration item string: " << m_instname << " " << m_field
    << " : from component ";
  if (m_inst_set_by) {
    cout << m_inst_set_by->name() << endl;
  } else {
    cout << "<global>" << endl;
  }
  cout << "Value = " << m_val << endl;
}

////////////

//------------------------------------------------------------------------------
// uvm_config_item_object implementation
//------------------------------------------------------------------------------

uvm_config_item_object::uvm_config_item_object(
  const std::string& instname,
  const std::string& field,
  uvm_component* inst_set_by,
  uvm_object* val
) : uvm_config_item(instname,field,inst_set_by,uvm_config_type_object) {
  m_val = val;
}

uvm_config_item_object::~uvm_config_item_object() { }

uvm_config_item_object* uvm_config_item_object::as_object() { return this; }

uvm_object* uvm_config_item_object::value() const { return m_val; }

void uvm_config_item_object::print() const {
  cout << "Configuration item object: " << m_instname << " " << m_field
    << " : from component ";
  if (m_inst_set_by) {
    cout << m_inst_set_by->name() << endl;
  } else {
    cout << "<global>" << endl;
  }
  if (m_val) {
    cout << "Object = " << *m_val << endl;
  } else {
    cout << "Object = <null>" << endl;
  }
}

////////////////

//------------------------------------------------------------------------------
// uvm_config implementation
//------------------------------------------------------------------------------

uvm_config::uvm_config() { }

uvm_config::~uvm_config() { }

void uvm_config::add_config_item(uvm_config_item* item) {
  m_vec.push_back(item);

}

uvm_config_item* uvm_config::get_config_item(
  uvm_config_type type,
  const std::string& instname,
  const std::string& field
) {
  string s;
  for (unsigned i = 0; i < m_vec.size(); i++) {
    uvm_config_item* c = m_vec[m_vec.size() - (i+1)];
    if (c->m_type != type) continue;
    if (!(is_match(c->m_instname, instname))) continue;
    if (!(is_match(c->m_field, field))) continue;
    return c;
  }
  return 0;
}

//------------------------------------------------------------------------------
// uvm_config_mgr implementation
//------------------------------------------------------------------------------

uvm_config_mgr* the_config_mgr = 0;

uvm_config_mgr* uvm_get_config_mgr() {
  if (!the_config_mgr) {
    the_config_mgr = new uvm_config_mgr();
  }
  return the_config_mgr;
}

uvm_config_mgr::uvm_config_mgr() {
  m_print_config_matches = false;
  m_global_config = 0;
}

uvm_config_mgr::~uvm_config_mgr() {
  delete m_global_config;
}

uvm_config* uvm_config_mgr::global_config() {
  if (!m_global_config) {
    m_global_config = new uvm_config();
  }
  return m_global_config;
}

void uvm_config_mgr::set_config_string(
  const std::string& instname,
  const std::string& field,
  const std::string& val
) {
  set_config_string(0,instname,field,val);
}

void uvm_config_mgr::set_config_object(
  const std::string& instname,
  const std::string& field,
  uvm_object* val,
  bool clone
) {
  set_config_object(0,instname,field,val,clone);
}

bool uvm_config_mgr::get_config_string(
  const std::string& instname,
  const std::string& field,
  std::string& val
) {
  return get_config_string(0,instname,field,val);
}

bool uvm_config_mgr::get_config_object(
  const std::string& instname,
  const std::string& field,
  uvm_object*& val,
  bool clone
) {
  return get_config_object(0,instname,field,val,clone);
}

////////////////////

void uvm_config_mgr::set_config_item(
  uvm_component* inst,
  uvm_config_item* item
) {
  if (inst) {
    inst->config()->add_config_item(item);
  } else {
    global_config()->add_config_item(item);
  }
}
  
void uvm_config_mgr::set_config_int(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  const sc_dt::sc_lv<4096>& val
) {
  uvm_config_item_int* item = 
    new uvm_config_item_int(instname,field,inst,val);
  if (inst) {
    inst->config()->add_config_item(item);
  } else {
    global_config()->add_config_item(item);
  }
}

void uvm_config_mgr::set_config_string(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  const std::string& val
) {
  uvm_config_item_string* item = 
    new uvm_config_item_string(instname,field,inst,val);
  if (inst) {
    inst->config()->add_config_item(item);
  } else {
    global_config()->add_config_item(item);
  }
}

void uvm_config_mgr::set_config_object(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  uvm_object* val,
  bool clone 
) {
  uvm_object* obj;
  if (clone) {
    obj = val->clone();
  } else {
    obj = val;
  } 
  uvm_config_item_object* item = 
    new uvm_config_item_object(instname,field,inst,obj);
  if (inst) {
    inst->config()->add_config_item(item);
  } else {
    global_config()->add_config_item(item);
  }
}

uvm_config_item_int* uvm_config_mgr::get_config_int_internal(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  sc_dt::sc_lv<4096>& val
) {
  uvm_config_item* item = get_config_item(
    uvm_config_type_int,
    inst,
    instname,
    field
  );
  if (!item) {
    return 0;
  }
  uvm_config_item_int* item_int = item->as_int(); 
  if (!item_int) {
    SC_REPORT_ERROR(UVM_CONFIG_INTERNAL_,"");
    return 0;
  }
  val = item_int->value();
  return item_int;
}


uvm_config_item_string* uvm_config_mgr::get_config_string(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  std::string& val
) {
  uvm_config_item* item = get_config_item(
    uvm_config_type_string,
    inst,
    instname,
    field
  );
  if (!item) {
    return 0;
  }
  uvm_config_item_string* item_string = item->as_string(); 
  if (!item_string) {
    SC_REPORT_ERROR(UVM_CONFIG_INTERNAL_,"");
    return 0;
  }
  val = item_string->value();
  if (print_config_matches()) {
    item->print_match(inst,instname,field);
    std::cout << "Value: " << val << std::endl;
  }
  return item_string;
}

uvm_config_item_object* uvm_config_mgr::get_config_object(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  uvm_object*& val,
  bool clone
) {
  uvm_config_item* item = get_config_item(
    uvm_config_type_object,
    inst,
    instname,
    field
  );
  if (!item) {
    return 0;
  }
  uvm_config_item_object* item_object = item->as_object(); 
  if (!item_object) {
    SC_REPORT_ERROR(UVM_CONFIG_INTERNAL_,"");
    return 0;
  }
  if (clone) {
    val = item_object->value()->clone();
  } else {
    val = item_object->value();
  }
  if (print_config_matches()) {
    item->print_match(inst,instname,field);
    std::cout << "Value: ";
    if (val) { cout << *val << std::endl; } else { cout << "<null-object>" << endl; }
  }
  return item_object;
}

uvm_config_item* uvm_config_mgr::get_config_item(
  uvm_config_type type,    
  uvm_component* inst,
  const std::string& instname,
  const std::string& field
) {
  // form the stack 
  uvm_config_stack stack;
  sc_object* parent = inst;
  while (parent) {
    uvm_component* comp = DCAST<uvm_component*>(parent);
    if (comp)
      stack.push_back(comp->config());
    parent = parent->get_parent_object();
  }
  stack.push_back(global_config());
  //
  int n = stack.size();
  for (int i = n-1; i >= 0; i--) {
    uvm_config* config = stack[i];
    uvm_config_item* item = config->get_config_item(type,instname,field);
    if (item) {
      return item;
    }
  } 
  return 0;
}

/////////////////////

void uvm_print_config_matches(bool b) {
  uvm_get_config_mgr()->print_config_matches(b);
}

bool uvm_config_mgr::print_config_matches() const {
  return m_print_config_matches;
}

void uvm_config_mgr::print_config_matches(bool b) {
  m_print_config_matches = b;
}

/////////////////////

//------------------------------------------------------------------------------
// implementation of global configuration functions
//------------------------------------------------------------------------------

void uvm_set_config_string(
  const std::string& instname,
  const std::string& field,
  const std::string& val
) {
  uvm_get_config_mgr()->set_config_string(0,instname,field,val);
}

void uvm_set_config_object(
  const std::string& instname,
  const std::string& field,
  uvm_object* val,
  bool clone
) {
  uvm_get_config_mgr()->set_config_object(0,instname,field,val,clone);
}

/////////////////////

} // namespace uvm

