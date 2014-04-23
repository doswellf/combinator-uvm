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
/*! \file uvm_ml_packer.h
  \brief Header file defining pack-unpack functionality for UVM-SC transactions.
*/
#ifndef UVM_ML_PACKER_H
#define UVM_ML_PACKER_H

#include "systemc.h"

using namespace std;
using namespace sc_dt;



#include "uvm_ml_adapter.h"
#include "base/uvm_packer.h"



namespace uvm {

#define UVM_ML_PACKING_BLOCK_SIZE_INT 131072

class ml_uvm_packer_rep_int;
typedef ml_uvm_packer_rep_int uvm_ml_packer_rep_int;

/*! \class uvm_ml_packer
  \brief ML packer base class.

  Base class maintaining basic attributes of the packer
*/
class uvm_ml_packer : public uvm_packer {
public:
  uvm_ml_packer();
  virtual ~uvm_ml_packer();
  virtual bool use_metadata() const;
  virtual void use_metadata(bool b);
  virtual void fill_uvm_ml_packed_obj(uvm_ml_packed_obj* v);
  virtual void set_from_uvm_ml_packed_obj(uvm_ml_packed_obj* v);

  static uvm_ml_packer& get_the_uvm_ml_packer();
};

/*! \class uvm_ml_packer_int
  \brief The ML packer class.

  Implements packing and unpacking for various types
*/
class uvm_ml_packer_int : public uvm_ml_packer {
public:
  uvm_ml_packer_int(); 
  ~uvm_ml_packer_int(); 

  virtual bool use_metadata() const;
  virtual void use_metadata(bool b);

  virtual void fill_uvm_ml_packed_obj(uvm_ml_packed_obj* v);
  virtual void set_from_uvm_ml_packed_obj(uvm_ml_packed_obj* v);

  virtual void reset();
  virtual int get_remaining_unpacked_bits();

  virtual uvm_ml_packer_int& operator << (bool a);
  virtual uvm_ml_packer_int& operator << (char a);
  virtual uvm_ml_packer_int& operator << (unsigned char a);
  virtual uvm_ml_packer_int& operator << (short a);
  virtual uvm_ml_packer_int& operator << (unsigned short a);
  virtual uvm_ml_packer_int& operator << (int a);
  virtual uvm_ml_packer_int& operator << (unsigned int a);
  virtual uvm_ml_packer_int& operator << (long a);
  virtual uvm_ml_packer_int& operator << (unsigned long a);
  virtual uvm_ml_packer_int& operator << (long long a);
  virtual uvm_ml_packer_int& operator << (unsigned long long a);
  
  virtual uvm_ml_packer_int& operator << (std::string a);
  virtual uvm_ml_packer_int& operator << (const char*);
 
  virtual uvm_ml_packer_int& operator << (uvm_object* a);
  virtual uvm_ml_packer_int& operator << (const uvm_object& a);
  virtual uvm_ml_packer_int& operator << (const sc_logic& a);
  virtual uvm_ml_packer_int& operator << (const sc_bv_base& a);
  virtual uvm_ml_packer_int& operator << (const sc_lv_base& a);
  virtual uvm_ml_packer_int& operator << (const sc_int_base& a);
  virtual uvm_ml_packer_int& operator << (const sc_uint_base& a);
  virtual uvm_ml_packer_int& operator << (const sc_signed& a);
  virtual uvm_ml_packer_int& operator << (const sc_unsigned& a);
  //template <class T> uvm_ml_packer_int& operator << (const std::vector<T>& a) {
  //  return uvm_packer::operator << (a);
  //}
  virtual uvm_ml_packer_int& operator << (const std::vector<bool>& a); 

  virtual uvm_ml_packer_int& operator >> (bool& a);
  virtual uvm_ml_packer_int& operator >> (char& a);
  virtual uvm_ml_packer_int& operator >> (unsigned char& a);
  virtual uvm_ml_packer_int& operator >> (short& a);
  virtual uvm_ml_packer_int& operator >> (unsigned short& a);
  virtual uvm_ml_packer_int& operator >> (int& a);
  virtual uvm_ml_packer_int& operator >> (unsigned int& a);
  virtual uvm_ml_packer_int& operator >> (long& a);
  virtual uvm_ml_packer_int& operator >> (unsigned long& a);
  virtual uvm_ml_packer_int& operator >> (long long& a);
  virtual uvm_ml_packer_int& operator >> (unsigned long long& a);
  virtual uvm_ml_packer_int& operator >> (std::string& a);
  virtual uvm_ml_packer_int& operator >> (uvm_object*& a);
  virtual uvm_ml_packer_int& operator >> (sc_logic& a);
  virtual uvm_ml_packer_int& operator >> (sc_bv_base& a);
  virtual uvm_ml_packer_int& operator >> (sc_lv_base& a);
  virtual uvm_ml_packer_int& operator >> (sc_int_base& a);
  virtual uvm_ml_packer_int& operator >> (sc_uint_base& a);
  virtual uvm_ml_packer_int& operator >> (sc_signed& a);
  virtual uvm_ml_packer_int& operator >> (sc_unsigned& a);
  //template <class T> uvm_ml_packer_int& operator >> (std::vector<T>& a) {
  //  return uvm_packer::operator >> (a);
 // }
  virtual uvm_ml_packer_int& operator >> (std::vector<bool>& a);

  virtual void pack_null();
  virtual void pack_obj_header(const std::string & type_name);
  virtual void * unpack_obj_header();
  virtual uvm_object * unpack_uvm_obj_header();
protected:
  void set_bits(unsigned* bits, unsigned nbits);
  unsigned* get_packed_bits_int();

  uvm_ml_packer_rep_int* m_rep_int;
};



//////////////

template <class T> void uvm_ml_packer_pack(
  const T& val,
  uvm_ml_packed_obj* p
) {
  //uvm_ml_packer pkr;
  static uvm_ml_packer& pkr = uvm_ml_packer::get_the_uvm_ml_packer();
  pkr << val;
  int packed_size = pkr.get_remaining_unpacked_bits();
  int max_size = uvm_ml::uvm_ml_utils::get_max_bits();
  if (packed_size > max_size) {
    char msg[1024];
    sprintf(msg,"\nuvm_object size is %d\n"
            "Max size is %d\n"
            //"uvm_object type is '%s'\n"
            "Consider increasing the maximum size limit with the "
            "irun option '-defineall UVM_PACK_MAX_SIZE=<size>'.",
             packed_size, max_size /*, val.get_type_name().c_str() */
           );
    /*
    sprintf(msg,"\nuvm_object size is %d\n"
            "Max size is %d\n"
            "uvm_object type is '%s'\n"
            "Consider increasing the maximum size limit with the "
            "irun option '-defineall UVM_PACK_MAX_SIZE=<size>'.",
             packed_size, max_size, val.get_type_name().c_str()
           );
           */

    uvm_ml::uvm_ml_utils::report_sc_error(ML_UVM_SIZE_LIMIT_, msg);

  }
  pkr.fill_uvm_ml_packed_obj(p);
  pkr.reset();
}

template <class T> void uvm_ml_packer_unpack_create(
  uvm_ml_packed_obj* p,
  T*& val,
  void*
) {
  val = new T();


  static uvm_ml_packer& pkr = uvm_ml_packer::get_the_uvm_ml_packer();
  pkr.set_from_uvm_ml_packed_obj(p);
  pkr >> *val;
  pkr.reset();
}

template <class T> void uvm_ml_packer_unpack_create(
  uvm_ml_packed_obj* p,
  T*& val,
  uvm_object*
) {
  T dummy;
  try {

    static uvm_ml_packer& pkr = uvm_ml_packer::get_the_uvm_ml_packer();
    pkr.set_from_uvm_ml_packed_obj(p);
    pkr >> val;
    // check if any unpack error happened;
    // only 2 kinds of errors are flagged:
    // too few bits or too many bits;
    // check for too few bits here, for
    // too many bits exception is thrown
    // which needs to be caught
    if (int rem = pkr.get_remaining_unpacked_bits()) { // implies too few bits
      char msg[1024];
      sprintf(msg,"\nFewer bits unpacked in SystemC than were packed "
              "for this uvm_object in foreign language. "
              "This may be due to a mismatch in class definitions "
              "across languages - the SystemC "
              "uvm_object is smaller in size\n"
              "uvm_object type is '%s'\n"
              "Number of remaining bits is %d\n",
               dummy.get_type_name().c_str(), rem 
             );
      SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    }
    pkr.reset();
  }
  // check if "too may bits" error happened
  catch( const sc_report& ex ) {
    if (strcmp(UVM_PACKER_UNPACK_INDEX_, ex.get_msg_type()) == 0) {
      // implies too may bits error
        uvm_ml::uvm_ml_utils::print_sc_report(ex);

      char msg[1024];
      sprintf(msg,"\nMore bits unpacked in SystemC than were packed "
              "for this uvm_object in foreign language. "
              "This may be due to a mismatch in class definitions "
              "across languages - the SystemC "
              "uvm_object is larger in size\n"
              "uvm_object type is '%s'\n",
               dummy.get_type_name().c_str()
             );
      SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    } else  {
      // not the error we are looking for, throw back
      throw(ex);
    }
  }
}


////////////////////////////////////

} // namespace uvm

#endif
