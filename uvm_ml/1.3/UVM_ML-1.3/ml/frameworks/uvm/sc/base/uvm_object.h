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

/*! \file uvm_object.h
  \brief Base class for UVM-SC objects.
*/

#ifndef UVM_OBJECT_H
#define UVM_OBJECT_H

#include "base/uvm_typed.h"
#include "base/uvm_ids.h"

#include "sysc/utils/sc_hash.h"

#include <string>
#include <iostream>
#include <vector>

//////////////

namespace uvm {

// forward declaration of uvm_packer used in uvm_object

class uvm_packer;


//------------------------------------------------------------------------------
//
// CLASS: uvm_object
//
// Base class for data objects. 
//
//------------------------------------------------------------------------------

/*! \class uvm_object
  \brief Base class for data objects.

  
*/
class uvm_object : public uvm_typed {
public:

  //----------------------------------------------------------------------------
  // Constructors and destructor
  //----------------------------------------------------------------------------

  uvm_object();
  uvm_object(const std::string& name);
  virtual ~uvm_object();

  //----------------------------------------------------------------------------
  // functions relating to name
  //
  // get_full_name() returns get_name()
  //----------------------------------------------------------------------------

  virtual void set_name(const std::string& name);
  virtual std::string get_name() const;
  virtual std::string get_full_name() const;
 
  //----------------------------------------------------------------------------
  // print, pack, unpack, copy, compare
  //
  // uvm_object methods that call the corresponding required overrides 
  // do_print(), do_pack(), do_unpack(), do_copy(), and do_compare()
  //----------------------------------------------------------------------------

  virtual void print(std::ostream& os) const;
  int pack(uvm_packer& p) const;
  int unpack(uvm_packer& p);
  void copy(const uvm_object* rhs);
  bool compare(const uvm_object* rhs) const;

  //----------------------------------------------------------------------------
  // clone
  //
  // Creates a clone by doing a create followed by a copy 
  //----------------------------------------------------------------------------

  uvm_object* clone() const;
  
  //----------------------------------------------------------------------------
  // get_type_name   -- Required override
  //
  // Return the type name of this class - e.g., "my_object".
  // Inherits this pure virtual method from base class uvm_typed.
  //----------------------------------------------------------------------------
 
  virtual std::string get_type_name() const = 0;
  
  //----------------------------------------------------------------------------
  // do_print  -- Required override
  //
  // Print the object to a stream
  //----------------------------------------------------------------------------

  virtual void do_print(std::ostream& os) const = 0;

  //----------------------------------------------------------------------------
  // do_pack, do_unpack  -- Required overrides
  //
  // Pack/unpack the object using an uvm_packer
  //----------------------------------------------------------------------------

  virtual void do_pack(uvm_packer& p) const = 0;
  virtual void do_unpack(uvm_packer& p) = 0;

  //----------------------------------------------------------------------------
  // do_copy  -- Required override
  //
  // Copy the data from another object into this one.
  //----------------------------------------------------------------------------
 
  virtual void do_copy(const uvm_object* rhs) = 0;

  //----------------------------------------------------------------------------
  // do_compare  -- Required override
  //
  // Compare the data of another object with this one. Return true if equal.
  //----------------------------------------------------------------------------

  virtual bool do_compare(const uvm_object* rhs) const = 0;

  //----------------------------------------------------------------------------
  // Commands to pack the object to vectors of bool, char, or int.
  // Each returns the number of bits in the packed object.
  //----------------------------------------------------------------------------

  int pack_bits(std::vector<bool>& v, uvm_packer* p = 0);
  int pack_bytes(std::vector<char>& v, uvm_packer* p = 0);
  int pack_ints(std::vector<int>& v, uvm_packer* p = 0);

  //----------------------------------------------------------------------------
  // Commands to unpack the object from vectors of bool, char, or int.
  // Each returns the size of the given vector.
  //----------------------------------------------------------------------------

  int unpack_bits(const std::vector<bool>& v, uvm_packer* p = 0);
  int unpack_bytes(const std::vector<char>& v, uvm_packer* p = 0);
  int unpack_ints(const std::vector<int>& v, uvm_packer* p = 0);

  friend std::ostream& operator<<( std::ostream& os, const uvm_object& obj );
  friend std::ostream& operator<<( std::ostream& os, const uvm_object* obj );

protected:

  std::string m_name; // the full name 
};

//////////////////////

//------------------------------------------------------------------------------
// Registration macros to register an uvm_object with the factory.
// 
// A registration macro should be invoked outside the uvm_object class
// declaration.
// A registration macro registers the given uvm_object with the factory, and
// defines the get_type_name() member method of the registered object.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// Use the macro below to register a simple non-templated uvm_object.
// The macro argument is the name of the class.
// The registered name with the factory is the same as the macro argument.
//------------------------------------------------------------------------------

#define UVM_OBJECT_REGISTER(t) \
static int uvm_object_register_dummy_##t = \
  uvm::uvm_factory::register_uvm_object_creator( #t,new t::uvm_object_creator_##t()); \
inline std::string t::get_type_name() const { return #t; }

//------------------------------------------------------------------------------
// Use the macro below to register a simple non-templated uvm_object, 
// with a different registered name (first argument) than its 
// class name (second argument).
// The registered name with the factory is the same as the first macro argument.
//------------------------------------------------------------------------------

#define UVM_OBJECT_REGISTER_ALIAS(name,t) \
static int uvm_object_register_dummy_##name##_##t = \
  uvm::uvm_factory::register_uvm_object_creator( #name,new t::uvm_object_creator_##t()); \
inline std::string t::get_type_name() const { return #name; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_objects with 
// one template parameter.
// The first macro argument is the class name, and the second macro argument
// is a specific value of the template parameter.
// Example usage: "UVM_OBJECT_REGISTER_T(myobj, int)".
// The registered name with the factory is a concatenation of the first
// and second arguments, separated by "_".
// e.g., "myobj_int".
//------------------------------------------------------------------------------

#define UVM_OBJECT_REGISTER_T(t,T) \
static int uvm_object_register_dummy_##t##_##T = \
  uvm::uvm_factory::register_uvm_object_creator( #t "_" #T, new t<T>::uvm_object_creator_##t()); \
template<> inline std::string t<T>::get_type_name() const { return #t "_" #T; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_objects with 
// one template parameter, when you do not want the default registered name.
// Specify the alternate registration name as the first macro argument.
// Example usage: "UVM_OBJECT_REGISTER_T_ALIAS(myname, myobj, int)".
// The registered name with the factory is the same as the first macro argument.
//------------------------------------------------------------------------------

#define UVM_OBJECT_REGISTER_T_ALIAS(name,t,T) \
static int uvm_object_register_dummy_##name##_##t = \
  uvm::uvm_factory::register_uvm_object_creator( #name, new t<T>::uvm_object_creator_##t()); \
template<> inline std::string t<T>::get_type_name() const { return #name; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_objects with 
// two template parameters.
// The first macro argument is the class name. 
// The second and third macro arguments are specific values of the 
// two template parameters.
// Example usage: "UVM_OBJECT_REGISTER_T2(myotherobj, int, int)".
// The registered name with the factory is a concatenation of the first,
// second, and third arguments, separated by "_". 
// e.g., "myotherobj_int_int".
//------------------------------------------------------------------------------

#define UVM_OBJECT_REGISTER_T2(t,T1,T2) \
static int uvm_object_register_dummy_##t##_##T1##_##T2 = \
  uvm::uvm_factory::register_uvm_object_creator( #t "_" #T1 "_" #T2, new t<T1,T2>::uvm_object_creator_##t()); \
template<> inline std::string t<T1,T2>::get_type_name() const { return #t "_" #T1 "_" #T2; }

//------------------------------------------------------------------------------
// Use the macro below for registering templated uvm_objects with 
// two template parameters, when you do not want the default registered name.
// Specify the alternate registration name as the first macro argument.
// Example usage: "UVM_OBJECT_REGISTER_T2_ALIAS(myname, myotherobj, int, int)".
// The registered name with the factory is the same as the first macro argument.
//------------------------------------------------------------------------------

#define UVM_OBJECT_REGISTER_T2_ALIAS(name,t,T1,T2) \
static int uvm_object_register_dummy_##name##_##t = \
  uvm::uvm_factory::register_uvm_object_creator( #name, new t<T1,T2>::uvm_object_creator_##t()); \
template<> inline std::string t<T1,T2>::get_type_name() const { return #name; }

//------------------------------------------------------------------------------
// Utility macro to instrument an uvm_object such that it can be registered
// with the factory.
// 
// The utility macro should be invoked inside the uvm_object class
// declaration.
// The utility macro
// - declares the uvm_object_creator_<classname> class used by the factory
//   to create an instance of this object. 
// - declares the get_type_name() member method inside the uvm_object class.
// - defines the << operator to print the uvm_object to a stream.
// - defines uvm_packer >> operators necessary for unpacking this object.
//------------------------------------------------------------------------------

#define UVM_OBJECT_UTILS(t) \
class uvm_object_creator_##t : public uvm::uvm_object_creator { \
public: \
  uvm::uvm_object* create(const std::string& name) { \
    uvm::uvm_object* _uvmsc_obj = new t(); \
    _uvmsc_obj->set_name(name); \
    return _uvmsc_obj; \
  } \
}; \
virtual std::string get_type_name() const; \
static uvm::uvm_object* create() { return new t(); } \
friend std::ostream& operator << (std::ostream& os, const t& h) { \
  h.print(os); \
  return os; \
} \
friend std::ostream& operator << (std::ostream& os, const t*& h) { \
  h->print(os); \
  return os; \
} \
friend uvm::uvm_packer& operator >> (uvm::uvm_packer& p, t*& h) { \
  if (p.use_metadata()) { \
    uvm::uvm_object* uvmsc_obj; \
    p >> uvmsc_obj; \
    if (!uvmsc_obj) { \
      h = new t(); \
      return p; \
    } \
    h = DCAST<t*>(uvmsc_obj); \
    if (!h) {  \
      SC_REPORT_ERROR(sc_core::UVM_UNPACK_DCAST_,""); \
    } \
  } else { \
    h = new t(); \
    h->unpack(p); \
  }   \
  return p; \
} \
friend uvm::uvm_packer& operator >> (uvm::uvm_packer& p, t& h) { \
  if (p.use_metadata()) { \
    t* pt; \
    p >> pt; \
    h = *pt; \
    delete pt; \
  } else { \
    h.unpack(p); \
  } \
  return p; \
}
} // namespace uvm

#endif
