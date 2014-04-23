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

/*! \file uvm_packer.h
  \brief Define packing and unpacking policy for UVM-SC objects.
*/

#ifndef UVM_PACKER_H
#define UVM_PACKER_H

#include "systemc.h"
#include "base/uvm_object.h"

namespace uvm {

#define UVM_PACKING_BLOCK_SIZE 4096

// forward declaration of internal class uvm_packer_rep

class uvm_packer_rep;

//------------------------------------------------------------------------------
//
// CLASS: uvm_packer
//
// Class that provides packing/unpacking policy for data objects.
//
//------------------------------------------------------------------------------

/*! \class uvm_packer
  \brief provides packing/unpacking policy for data objects.

  
*/
class uvm_packer {
public:
  friend class uvm_object;

  //----------------------------------------------------------------------------
  // Constructor and destructor
  //----------------------------------------------------------------------------

  uvm_packer();
  virtual ~uvm_packer();

  //----------------------------------------------------------------------------
  // Metadata
  //----------------------------------------------------------------------------

  virtual bool use_metadata() const;
  virtual void use_metadata(bool b);
  
  //----------------------------------------------------------------------------
  // Size of packed bits 
  //----------------------------------------------------------------------------

  int get_size();
  void set_size(int nbits);

  //----------------------------------------------------------------------------
  // Operator << for data types that can be packed using this class
  //
  // These will be invoked from uvm_object's do_pack() method
  //----------------------------------------------------------------------------

  virtual uvm_packer& operator << (bool a);
  virtual uvm_packer& operator << (char a);
  virtual uvm_packer& operator << (unsigned char a);
  virtual uvm_packer& operator << (short a);
  virtual uvm_packer& operator << (unsigned short a);
  virtual uvm_packer& operator << (int a);
  virtual uvm_packer& operator << (unsigned int a);
  virtual uvm_packer& operator << (long a);
  virtual uvm_packer& operator << (unsigned long a);
  virtual uvm_packer& operator << (long long a);
  virtual uvm_packer& operator << (unsigned long long a);
  
  virtual uvm_packer& operator << (std::string a);
  virtual uvm_packer& operator << (const char*);
 
  virtual uvm_packer& operator << (uvm_object* a);
  virtual uvm_packer& operator << (const uvm_object& a);
  virtual uvm_packer& operator << (const sc_logic& a);
  virtual uvm_packer& operator << (const sc_bv_base& a);
  virtual uvm_packer& operator << (const sc_lv_base& a);
  virtual uvm_packer& operator << (const sc_int_base& a);
  virtual uvm_packer& operator << (const sc_uint_base& a);
  virtual uvm_packer& operator << (const sc_signed& a);
  virtual uvm_packer& operator << (const sc_unsigned& a);
  template <class T> 
  uvm_packer& operator << (const std::vector<T>& a) {
    // first pack the size of the vector before packing its elements
    int n = a.size();
    (*this) << n;
    for (int i = 0; i < n; i++) {
      (*this) << a[i];
    }
    return *this;
  }

  virtual uvm_packer& operator << (const std::vector<bool>& a) {
    // first pack the size of the vector before packing its elements
    int n = a.size();
    (*this) << n;
    for (int i = 0; i < n; i++) {
      (*this) << a[i];
    }
    return *this;
  }

  //----------------------------------------------------------------------------
  // Operator >> for data types that can be unpacked using this class
  //
  // These will be invoked from uvm_object's do_unpack() method
  //----------------------------------------------------------------------------
 
  virtual uvm_packer& operator >> (bool& a);
  virtual uvm_packer& operator >> (char& a);
  virtual uvm_packer& operator >> (unsigned char& a);
  virtual uvm_packer& operator >> (short& a);
  virtual uvm_packer& operator >> (unsigned short& a);
  virtual uvm_packer& operator >> (int& a);
  virtual uvm_packer& operator >> (unsigned int& a);
  virtual uvm_packer& operator >> (long& a);
  virtual uvm_packer& operator >> (unsigned long& a);
  virtual uvm_packer& operator >> (long long& a);
  virtual uvm_packer& operator >> (unsigned long long& a);
  virtual uvm_packer& operator >> (std::string& a);
  virtual uvm_packer& operator >> (uvm_object*& a);
  virtual uvm_packer& operator >> (sc_logic& a);
  virtual uvm_packer& operator >> (sc_bv_base& a);
  virtual uvm_packer& operator >> (sc_lv_base& a);
  virtual uvm_packer& operator >> (sc_int_base& a);
  virtual uvm_packer& operator >> (sc_uint_base& a);
  virtual uvm_packer& operator >> (sc_signed& a);
  virtual uvm_packer& operator >> (sc_unsigned& a);
  template <class T> 
  uvm_packer& operator >> (std::vector<T>& a) {
    a.clear();
    int n;
    // first unpack the size of the vector before unpacking its elements
    (*this) >> n;
    for (int i = 0; i < n; i++) {
      T t;
      (*this) >> t;
      a.push_back(t);
    }
    return *this;
  }

  virtual uvm_packer& operator >> (std::vector<bool>& a) {
    a.clear();
    int n;
    // first unpack the size of the vector before unpacking its elements
    (*this) >> n;
    for (int i = 0; i < n; i++) {
      bool t;
      (*this) >> t;
      a.push_back(t);
    }
    return *this;
  }

  // methods primarily for internal use

  sc_bv_base* get_packed_bits();
  
  virtual void reset();
  virtual int get_remaining_unpacked_bits();

  void put_bits(const std::vector<bool>& v);
  void get_bits(std::vector<bool>& v);
  void put_bytes(const std::vector<char>& v);
  void get_bytes(std::vector<char>& v);
  void put_ints(const std::vector<int>& v);
  void get_ints(std::vector<int>& v);
  void put_uints(const std::vector<unsigned int>& v);
  void get_uints(std::vector<unsigned int>& v);

  virtual void pack_null();
  virtual void pack_obj_header(const std::string & type_name);
  virtual void * unpack_obj_header();

protected:
  int get_pack_index() const;
  void set_pack_index(int n);
  //
  uvm_packer_rep* m_rep; // internal implementation class 
};

typedef unsigned (*get_id_type)(std::string name);
typedef char* (*get_name_type)(unsigned id);
 
//void set_get_id_func_ptr(get_id_type ptr);
//void set_get_name_func_ptr(get_name_type ptr);


} // namespace uvm

#endif
