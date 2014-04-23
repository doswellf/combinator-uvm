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

/*! \file uvm_object.cpp
  \brief Base class for UVM-SC objects.
*/

#include "base/uvm_object.h"
#include "base/uvm_factory.h"
#include "base/uvm_packer.h"

using namespace std;

namespace uvm {

//------------------------------------------------------------------------------
//
// uvm_object
//
//------------------------------------------------------------------------------


uvm_object::uvm_object() { m_name = ""; }

uvm_object::uvm_object(const std::string& name) { m_name = name; }

uvm_object::~uvm_object() { }

void uvm_object::set_name(const string& name) {
  m_name = name;
}

string uvm_object::get_name() const {
  return m_name;
}

std::string uvm_object::get_full_name() const {
  return m_name;
}

void uvm_object::print(ostream& os) const { 
  do_print(os);
}

ostream& operator<<( ostream& os, const uvm_object& obj ) {
  obj.print(os);
  return os;
}

ostream& operator<<( ostream& os, const uvm_object* obj ) {
  obj->print(os);
  return os;
}

// clone() first creates a new object and then copies the existing object
// into the new object.
// returns the new object

uvm_object* uvm_object::clone() const {
  uvm_object* obj = uvm_factory::create_uvm_object(get_type_name(),"","",true);
  obj->copy(this);
  return obj;
}

int uvm_object::pack(uvm_packer& p) const {
  do_pack(p);
  return p.get_remaining_unpacked_bits();
}

int uvm_object::unpack(uvm_packer& p) {
  do_unpack(p);
  return p.get_remaining_unpacked_bits();
}

void uvm_object::copy(const uvm_object* rhs) {
  do_copy(rhs);
}

bool uvm_object::compare(const uvm_object* rhs) const {
  bool b = do_compare(rhs);
  return b;
}

///////////

// default implementations of required overrides

void uvm_object::do_print(ostream& os) const {
  os << get_type_name() << endl;
}

void uvm_object::do_pack(uvm_packer& ) const { }

void uvm_object::do_unpack(uvm_packer& ) { }

void uvm_object::do_copy(const uvm_object* rhs) { }

bool uvm_object::do_compare(const uvm_object* rhs) const { return true; }

///////////

static uvm_packer pp;

int uvm_object::pack_bits(std::vector<bool>& v, uvm_packer* p) {
  //static uvm_packer pp;
  if (!p) { pp.reset(); p = &pp; }
  pack(*p);
  p->get_bits(v);
  int n = p->get_remaining_unpacked_bits();
  return n;
}

int uvm_object::unpack_bits(const std::vector<bool>& v, uvm_packer* p) {
  //static uvm_packer pp;
  if (!p) { pp.reset(); p = &pp; }
  p->put_bits(v);
  unpack(*p);
  return v.size();
}

int uvm_object::pack_bytes(std::vector<char>& v, uvm_packer* p) {
  //static uvm_packer pp;
  if (!p) { pp.reset(); p = &pp; }
  pack(*p);
  p->get_bytes(v);
  int n = p->get_remaining_unpacked_bits();
  return n;
}

int uvm_object::unpack_bytes(const std::vector<char>& v, uvm_packer* p) {
  //static uvm_packer pp;
  if (!p) { pp.reset(); p = &pp; }
  p->put_bytes(v);
  unpack(*p);
  return v.size();
}

int uvm_object::pack_ints(std::vector<int>& v, uvm_packer* p) {
  //static uvm_packer pp;
  if (!p) { pp.reset(); p = &pp; }
  pack(*p);
  p->get_ints(v);
  int n = p->get_remaining_unpacked_bits();
  return n;
}

int uvm_object::unpack_ints(const std::vector<int>& v, uvm_packer* p) {
  //static uvm_packer pp;
  if (!p) { pp.reset(); p = &pp; }
  p->put_ints(v);
  unpack(*p);
  return v.size();
}

///////////

} // namespace uvm
