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
/*! \file uvm_ml_packer.cpp
  \brief Implementing pack-unpack for UVM-SC transactions.
*/
#include "systemc.h"
#include "uvm_ml_adapter_imp_spec_macros.h"
#include "uvm_ml_adapter_imp_spec_headers.h"
#include "common/uvm_ml_packer.h"

#include "common/ml_tlm2/ml_tlm2_connector.h"

#include <typeinfo>
#include <iostream>


#include "base/uvm_factory.h"
#include "base/uvm_packer.h"
#include "base/uvm_object.h"

using namespace std;

namespace uvm {

/////////////////////////////

// debugging aid to print informative messages when packing/unpacking

bool print_pack_info_int = getenv("print_pack_info");

/////////////////////////////

uvm_ml_packer::uvm_ml_packer() {
  uvm_packer::use_metadata(true);
}

uvm_ml_packer::~uvm_ml_packer() { }

bool uvm_ml_packer::use_metadata() const {
  return uvm_packer::use_metadata();
}

void uvm_ml_packer::use_metadata(bool b) {
  if (!b) {
    cerr << "WARNING: uvm_ml_packer use_metadata must be true. " 
      << "Ignoring attempt to set it to false" << endl;
    return;
  }
}

void uvm_ml_packer::set_from_uvm_ml_packed_obj(uvm_ml_packed_obj* v) {
  set_size(v->size/32);
  int size = get_size();
  sc_bv_base btmp(size);
  int nwords = btmp.size(); // # words that will fit in size bits
  sc_bv_base* bv = get_packed_bits();
  for (int i = 0; i < nwords; i++) {
    bv->set_word(i, *(v->val + i));
  }
  set_pack_index(nwords);
}

void uvm_ml_packer::fill_uvm_ml_packed_obj(uvm_ml_packed_obj* v) {
  v->size = get_pack_index() * 32;
  sc_bv_base* bv = get_packed_bits();
  int size = get_size();
  sc_bv_base btmp(size);
  int bsize = btmp.size(); // # words that will fit in size bits

  // this mlupo is going over to backplane and then onto SV adaptor;
  // the SV adaptor is hardcoded to accept the max bits, hence allocate
  // max words here

  static int nwords = uvm_ml::uvm_ml_utils::get_max_words();

  uvm_ml_packed_obj::allocate(v, nwords);

  for (int i = 0; i < bsize; i++) {
    *(v->val + i) = bv->get_word(i);
  }
}

static uvm_ml_packer the_uvm_ml_packer;
static uvm_ml_packer_int the_uvm_ml_packer_int;

uvm_ml_packer& uvm_ml_packer::get_the_uvm_ml_packer() {
  return the_uvm_ml_packer_int;
}

/////////////////////////////

// NOTE: unlimited max size 
// memory is allocated dynamically in chunks of 
// unsigned(UVM_ML_PACKING_BLOCK_SIZE_INT)


//------------------------------------------------------------------------------
//
// CLASS: ml_uvm_packer_rep_int
//
// Internal implementation class.
// uvm_packer delegetates to this class to do the real work.
//
//---------------------------------------------------------------------------

/*! \class ml_uvm_packer_rep_int
  \brief ML UVM packer implementation.

  Internal implementation, uvm_packer delegetates to this class to do the real work
*/
class ml_uvm_packer_rep_int {
public:
  ml_uvm_packer_rep_int(uvm_packer* packer);
  ~ml_uvm_packer_rep_int();
  //
  void allocate(int nwords, bool copy = true);
  void reset();
  void set_bits(unsigned* bits, unsigned nbits);
  //
  bool use_metadata() const { return m_use_metadata; }
  void use_metadata(bool b) { m_use_metadata = b; }
  //
  void check_size(int nwords);
  //
  void pack_non_null();
  bool unpack_non_null();
  void pack_null();
  //
  void pack_char(char);
  void unpack_char(char&);
  //
  void pack_string(std::string s);
  void unpack_string(std::string& s);
  //
  void pack_obj_header(const std::string & type_name);
  void * unpack_obj_header();
  uvm_object * unpack_uvm_obj_header();
  void pack_obj(uvm_object*);
  void unpack_obj(uvm_object*&);
  //
  void pack_sc_logic(const sc_logic&);
  void unpack_sc_logic(sc_logic&);
  void pack_sc_bv_base(const sc_bv_base&);
  void unpack_sc_bv_base(sc_bv_base&);
  void pack_sc_lv_base(const sc_lv_base&);
  void unpack_sc_lv_base(sc_lv_base&);
  void pack_sc_int_base(const sc_int_base&);
  void unpack_sc_int_base(sc_int_base&);
  void pack_sc_uint_base(const sc_uint_base&);
  void unpack_sc_uint_base(sc_uint_base&);
  void pack_sc_signed(const sc_signed&);
  void unpack_sc_signed(sc_signed&);
  void pack_sc_unsigned(const sc_unsigned&);
  void unpack_sc_unsigned(sc_unsigned&);
  //
  unsigned get_remaining_unpacked_bits() { return (pack_index - unpack_index) * 32; }
  unsigned* get_packed_bits() { return m_bits; }
  int get_pack_index() const { return pack_index; }
  void inc_unpack_index(int n);
  uvm_packer* m_packer;
  bool m_use_metadata;
  unsigned pack_index;
  unsigned unpack_index;

  unsigned* m_bits;
  unsigned size;
  unsigned max_size;
};



template<typename T>
void pack_unsigned(const T& a, uvm_ml_packer_rep_int* rep) {
  unsigned nwords = (sizeof(T)*8 - 1)/32 + 1;
  rep->check_size(nwords);
  memcpy(&(rep->m_bits[rep->pack_index]), &a, sizeof(T));
  rep->pack_index+= nwords;
}

template<typename T>
void unpack_unsigned(T& a, uvm_ml_packer_rep_int* rep) {
  unsigned nwords = (sizeof(T)*8 - 1)/32 + 1;
  memcpy(&a, &(rep->m_bits[rep->unpack_index]), sizeof(T));
  rep->inc_unpack_index(nwords);
}

static sc_strhash<void*> name_id_dict;
static sc_phash<void*, std::string*> id_name_dict;

unsigned uvm_get_type_id(std::string name) {
  char* c = (char*)(name.c_str());
  unsigned id = 0;
  void* pid = 0;
  if (name_id_dict.contains(c)) {
    pid = name_id_dict[c];
    id = (unsigned)(unsigned long)(pid);
    return id;
  }
  // not in dict
  id = uvm_ml::uvm_ml_utils::get_type_id(name);
  pid = (void*)(unsigned long)(id);
  name_id_dict.insert(c, pid);
  return id;
}

std::string uvm_get_type_name(unsigned id) {
  std::string *name = 0;
  void* pid;
  // need to do the cast to unsigned long below before casting to pointer
  // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
  // bits; so casting from unsigned to pointer generates compiler warning;
  // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
  pid = (void *)(unsigned long)id;
    name = id_name_dict[pid];
    if (name != 0) {
    return *name;
  }
  // not in dict
  char* nm = uvm_ml::uvm_ml_utils::get_type_name(id);
  name = new std::string(nm); 
  id_name_dict.insert(pid, name);
  return *name;
}

//------------------------------------------------------------------------------
// uvm_ml_packer_rep_int implementation
//------------------------------------------------------------------------------

ml_uvm_packer_rep_int::ml_uvm_packer_rep_int(uvm_packer* packer) {
  m_packer = packer;
  m_use_metadata = false;

  pack_index = 0;
  unpack_index = 0;

  size = 0;
  max_size = 0;
  m_bits = 0;
}

ml_uvm_packer_rep_int::~ml_uvm_packer_rep_int() {
  if (m_bits)
    delete[] m_bits;
}

void ml_uvm_packer_rep_int::allocate(int nwords, bool copy_) {
  // allocate new unsigned array with new size, and copy over contents from
  // old unsigned array

  unsigned total_elems = pack_index + nwords;
  unsigned old_size = size;
  size = ((total_elems - 1)/UVM_ML_PACKING_BLOCK_SIZE_INT + 1)*UVM_ML_PACKING_BLOCK_SIZE_INT; 
  // the calculation above is simply adding a chunk of 
  // UVM_ML_PACKING_BLOCK_SIZE_INT elements to the existing 
  // size; instead of doing that directly, we go thru the calcualtions in case 
  // (nwords > UVM_ML_PACKING_BLOCK_SIZE_INT), in which case more 
  // than 1 chunk will be added;
  
  if (size > max_size) { // need to allocate
    max_size = size;
    unsigned* new_bv = new unsigned[size];
    if (m_bits) {
      if (copy_) {
        memcpy(new_bv, m_bits, old_size*(sizeof(unsigned)));
      }
      delete[] m_bits;
    }
    m_bits = new_bv;
    return;
  }
}
  
void ml_uvm_packer_rep_int::set_bits(unsigned* bits, unsigned nbits) {

    unsigned nwords = nbits/32;
  // check that we are in a "fresh" packer, e.g. one that has been reset

    ASSERT_ZERO(size);
    ASSERT_ZERO(pack_index);
  // no need to copy over from old sc_bv_base
  allocate(nwords, false);  
  memcpy(m_bits, bits, nwords*sizeof(unsigned));
  size = nwords;
  pack_index = nwords;
}

void ml_uvm_packer_rep_int::reset() {

  pack_index = 0;
  unpack_index = 0;
  size = 0;
}

void ml_uvm_packer_rep_int::inc_unpack_index(int n) {
  unpack_index += n;
  if (unpack_index > pack_index) {
    char msg[1024];
    sprintf(msg,"unpack_index=%d, pack_index=%d",unpack_index,pack_index);
    SC_REPORT_ERROR(UVM_PACKER_UNPACK_INDEX_,msg);
  }
}

////////

void ml_uvm_packer_rep_int::check_size(int nwords) {
  int capacity = size - pack_index;
  if (nwords >= capacity) {
    allocate(nwords);
  }
}

// put a 8-bit 1 meaning non-null for uvm_objects

void ml_uvm_packer_rep_int::pack_non_null() {
  int i = 1;
  pack_unsigned(i, this);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_non_null " << endl;
}

// put 8-bit 0 meaning null for uvm_objects

void ml_uvm_packer_rep_int::pack_null() {
  int i = 0;
  pack_unsigned(i, this);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_null " << endl;
}

bool ml_uvm_packer_rep_int::unpack_non_null() {
  int a;
  unpack_unsigned(a, this);
  if (!a) { 
    if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_non_null FALSE " << endl;
    return false;
  }
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_non_null true " << endl;
  return true;
}

////////

void ml_uvm_packer_rep_int::pack_char(char a) {
  pack_unsigned(a, this);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_char " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_char(char& a) {
  unpack_unsigned(a, this);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_char -> " << a << endl;
}

////////

// after packing a string, pack a null byte at the end 

void ml_uvm_packer_rep_int::pack_string(std::string a) {

  int nchars = a.length() + 1; // length + terminating null char
  const char* cstring = a.c_str();  // cstring is null terminated

  // pack 4 chars in each slot, and pack a null char at end
  unsigned nwords = (nchars - 1)/4 + 1;
  unsigned nwords_minusone = nwords - 1;
  check_size(nwords);
  // first copy over nwords-1 
  for (unsigned i=0; i < nwords_minusone; i++) {      
#if defined(_AIX) || defined(sparc)
    char c[4];
    c[0] = cstring[i*4+3];
    c[1] = cstring[i*4+2];
    c[2] = cstring[i*4+1];
    c[3] = cstring[i*4];
    memcpy(&(m_bits[pack_index]), c, 4);
#else
    memcpy(&(m_bits[pack_index]), &(cstring[i*4]), 4);
#endif
    pack_index++;
  }
  // now copy over the remaining chars
  unsigned remainder = nchars - (nwords_minusone * 4);
#if defined(_AIX) || defined(sparc)
  char c[4];
  for (unsigned i=0; i < 4; i++) {      
    unsigned index = nwords*4-i-1;
    if (index > (nwords_minusone*4+remainder-1)) 
      c[i] = 0;
    else
      c[i] = cstring[index];
   }
   memcpy(&(m_bits[pack_index]), c, 4);
#else
  memcpy(&(m_bits[pack_index]), &(cstring[nwords_minusone*4]), remainder);
#endif
  pack_index++;

  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_string " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_string(std::string& a) {

  a = "";
  std::string cs;
  char c[4];
  while (1) {
    unsigned sz = 4;
    bool done = false;
    memcpy(c, &(m_bits[unpack_index]), 4);
    inc_unpack_index(1);
#if defined(_AIX) || defined(sparc)
    char tmp;
    tmp = c[0]; c[0] = c[3]; c[3] = tmp;
    tmp = c[1]; c[1] = c[2]; c[2] = tmp;
#endif
    // check each slot if it is the null char 
    if (!c[0]) {
      sz = 0; done = true;
    } else if (!c[1]) {
      sz = 1; done = true;
    } else if (!c[2]) {
      sz = 2; done = true;
    } else if (!c[3]) {
      sz = 3; done = true;
    }
    if (sz > 0) { 
      cs.assign(c, sz);
      a = a + cs;
    }
    if (done)
      break;
  }

  if (print_pack_info_int) 
    cerr << "ml_uvm_packer_rep_int::unpack_string: " << a << endl;
}

void ml_uvm_packer_rep_int::pack_obj_header(const std::string & type_name)
{
  pack_non_null();
  pack_unsigned(uvm_get_type_id(type_name), this);
}

// metadata affects how a nested uvm_object is packed.
// if metadata is included, then before packing the uvm_object, pack 2
// additional items:
// 1) 8 bits set to 1 if the uvm_object is non-null, and set 
// to 0 if uvm_object is null
// 2) the string name of the uvm_object, as returned by get_type_name()

void ml_uvm_packer_rep_int::pack_obj(uvm_object* a) {
  if (use_metadata()) {
    if (a == NULL) {
      if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_obj packing null" << endl;
      pack_null();
      return;
    }
    pack_non_null();
    std::string s = a->get_type_name();
    unsigned id = uvm_get_type_id(s);
    pack_unsigned(id, this);
  }
  if (!a) {
    SC_REPORT_ERROR(UVM_PACK_NULL_,"");
    return;
  }
  a->pack(*m_packer);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_obj " 
    << a->get_type_name() << endl;
}

void * ml_uvm_packer_rep_int::unpack_obj_header() {
  std::string s;
  if (!unpack_non_null()) {
    if (print_pack_info_int)
      cerr << "ml_uvm_packer_rep_int::unpack_obj_header unpack_non_null FALSE" << endl;
    return NULL;
  }
  unsigned id = 0;
  unpack_unsigned(id, this);
  s = uvm_get_type_name(id);
  void *obj = NULL;
  string base_class_str;
  if (uvm_factory::is_uvm_object_registered(s)) {
    base_class_str = "uvm_object";
    obj = (void *) uvm_factory::create_uvm_object(s,"","",true);
  } else if (uvm_factory::is_class_registered(s)) {
    base_class_str = "tlm_generic_payload";
    obj = uvm_factory::create_registered_class(s);
  }
  if (!obj) {
    char msg[1024];
    sprintf(msg,"Unpack %s failed. Type = %s",base_class_str.c_str(), s.c_str());
    SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    return NULL;
  }
  return obj;
}

uvm_object * ml_uvm_packer_rep_int::unpack_uvm_obj_header() {
  std::string s;
  if (!unpack_non_null()) {
    if (print_pack_info_int)
      cerr << "ml_uvm_packer_rep_int::unpack_obj_header unpack_non_null FALSE" << endl;
    return NULL;
  }
  unsigned id = 0;
  unpack_unsigned(id, this);
  s = uvm_get_type_name(id);
  uvm_object *obj = NULL;
  string base_class_str;
  if (uvm_factory::is_uvm_object_registered(s)) {
    base_class_str = "uvm_object";
    obj = uvm_factory::create_uvm_object(s,"","",true);
  } 
  if (!obj) {
    char msg[1024];
    sprintf(msg,"Unpack %s failed. Type = %s",base_class_str.c_str(), s.c_str());
    SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    return NULL;
  }
  return obj;
}


// metadata affects how a nested uvm_object is unpacked.
// metadata must have been packed during the corresponding packing
// operation, as the packer allocates/creates the uvm_object from the
// factory using the packed type name.
// if metadata was not packed, then the packer errors out.

void ml_uvm_packer_rep_int::unpack_obj(uvm_object*& a) {
  if (!use_metadata()) {
    SC_REPORT_ERROR(UVM_UNPACK_OBJ_NO_METADATA_,"");
    a = 0;
    return;
  }
  std::string s;
  if (!unpack_non_null()) {
    if (print_pack_info_int) {
      cerr << "ml_uvm_packer_rep_int::unpack unpack_non_null FALSE" << endl;
    }
    a = 0;
    return;
  }
  unsigned id = 0;
  unpack_unsigned(id, this);
  s = uvm_get_type_name(id);
  uvm_object* obj = uvm_factory::create_uvm_object(s,"","",true);
  if (!obj) {
    char msg[1024];
    sprintf(msg,"Unpack uvm_object failed. Type = %s",s.c_str());
    SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    return;
  }
  obj->unpack(*m_packer);
  a = obj;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_obj " << endl;
}

void ml_uvm_packer_rep_int::pack_sc_logic(const sc_logic& a) {
  check_size(1);
  if (int(a.value()) == int(sc_dt::Log_1)) {
    m_bits[pack_index] = 1;
  } else {
    m_bits[pack_index] = 0;
  }
  pack_index++;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_logic " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_logic(sc_logic& a) {
  if (m_bits[unpack_index] == 1) {
    a = sc_dt::Log_1;
  } else {
    a = sc_dt::Log_0;
  }
  inc_unpack_index(1);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_logic " << a << endl;
}

void ml_uvm_packer_rep_int::pack_sc_bv_base(const sc_bv_base& a) {
  unsigned nwords = a.size(); 
  check_size(nwords);
#ifdef NC_SYSTEMC
  memcpy(&(m_bits[pack_index]), a.m_data, nwords*4);
#else
  // m_data is protected in OSCI
  for(unsigned int i = 0; i < nwords; i++) m_bits[pack_index+i] = a.get_word(i);
#endif
  pack_index += nwords;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_bv_base " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_bv_base(sc_bv_base& a) {
  int nwords = a.size();
#ifdef NC_SYSTEMC
  memcpy(a.m_data, &(m_bits[unpack_index]), nwords*4);
#else
  // m_data is 'protected' in OSCI
  for(int i = 0; i < nwords; i++) a.set_word(i, (sc_digit)m_bits[unpack_index+i]);
#endif
  inc_unpack_index(nwords);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_bv_base " << a << endl;
}

void ml_uvm_packer_rep_int::pack_sc_lv_base(const sc_lv_base& a) {
  unsigned nwords = a.size(); 
  check_size(nwords);
#ifdef NC_SYSTEMC
  memcpy(&(m_bits[pack_index]), a.m_data, nwords*4);
#else
  // m_data is 'protected' in OSCI
  for(unsigned int i = 0; i < nwords; i++) m_bits[pack_index+i] = a.get_word(i);
#endif
  pack_index += nwords;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_lv_base " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_lv_base(sc_lv_base& a) {
  int nwords = a.size();
#ifdef NC_SYSTEMC
  memcpy(a.m_data, &(m_bits[unpack_index]), nwords*4);
#else
  // m_data is 'protected' in OSCI
  for(int i = 0; i < nwords; i++) a.set_word(i, (sc_digit)m_bits[unpack_index+i]);
#endif
  inc_unpack_index(nwords);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_lv_base " << a << endl;
}

void ml_uvm_packer_rep_int::pack_sc_int_base(const sc_int_base& a) {

  int nbits = a.length();
  int nwords = (nbits - 1)/32 + 1;
  check_size(nwords);
  if (nwords == 1) {
    int i = a.to_int();
    m_bits[pack_index] = i;
  } else {
    int64 i = a.to_int64();
    memcpy(&(m_bits[pack_index]), &i, 2*sizeof(unsigned));
  } 
  pack_index += nwords;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_int_base " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_int_base(sc_int_base& a) {

  int nbits = a.length(); 
  int nwords = (nbits - 1)/32 + 1;
  if (nwords == 1) {
    a = m_bits[unpack_index];
  } else {
    int64 i;
    memcpy(&i, &(m_bits[unpack_index]), 2*sizeof(unsigned));
    a = i;
  }
  inc_unpack_index(nwords);  
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_int_base " << a << endl;
}

void ml_uvm_packer_rep_int::pack_sc_uint_base(const sc_uint_base& a) {

  int nbits = a.length();
  int nwords = (nbits - 1)/32 + 1;
  check_size(nwords);
  if (nwords == 1) {
    unsigned u = a.to_uint();
    m_bits[pack_index] = u;
  } else {
    uint64 u = a.to_uint64();
    memcpy(&(m_bits[pack_index]), &u, 2*sizeof(unsigned));
  } 
  pack_index += nwords;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_uint_base " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_uint_base(sc_uint_base& a) {
  int nbits = a.length(); 
  int nwords = (nbits - 1)/32 + 1;

  ASSERT_N_WORDS(nwords, 3);

  if (nwords == 1) {
    a = m_bits[unpack_index];
  } else {
    uint64 u;
    memcpy(&u, &(m_bits[unpack_index]), 2*sizeof(unsigned));
    a = u;
  }
  inc_unpack_index(nwords);  
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_uint_base " << a << endl;
}

void ml_uvm_packer_rep_int::pack_sc_signed(const sc_signed& a) {
  unsigned nbits = a.length(); 
  unsigned nwords = (nbits - 1)/32 + 1;
  check_size(nwords);
  // the internal representation inside sc_signed is not exactly
  // the same as the representation in m_bits, so cannot do memcpy()
  a.get_packed_rep(&(m_bits[pack_index]));
  pack_index += nwords;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_signed " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_signed(sc_signed& a) {
  int nbits = a.length();
  int nwords = (nbits - 1)/32 + 1;
  // the internal representation inside sc_signed is not exactly
  // the same as the representation in m_bits, so cannot do memcpy()
  a.set_packed_rep(&(m_bits[unpack_index]));
  inc_unpack_index(nwords);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_signed " << a << endl;
}

void ml_uvm_packer_rep_int::pack_sc_unsigned(const sc_unsigned& a) {
  unsigned nbits = a.length(); 
  unsigned nwords = (nbits - 1)/32 + 1;
  check_size(nwords);
  // the internal representation inside sc_unsigned is not exactly
  // the same as the representation in m_bits, so cannot do memcpy()
  a.get_packed_rep(&(m_bits[pack_index]));
  pack_index += nwords;
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::pack_sc_unsigned " << a << endl;
}

void ml_uvm_packer_rep_int::unpack_sc_unsigned(sc_unsigned& a) {
  int nbits = a.length();
  int nwords = (nbits - 1)/32 + 1;
  // the internal representation inside sc_unsigned is not exactly
  // the same as the representation in m_bits, so cannot do memcpy()
  a.set_packed_rep(&(m_bits[unpack_index]));
  inc_unpack_index(nwords);
  if (print_pack_info_int) cerr << "ml_uvm_packer_rep_int::unpack_sc_unsigned " << a << endl;
}

/////////////////////////////

//----------------------------------------------------------------------
// uvm_ml_packer_int implementation
//----------------------------------------------------------------------

uvm_ml_packer_int::uvm_ml_packer_int() {
  m_rep_int = new uvm_ml_packer_rep_int(this);
  m_rep_int->use_metadata(true);
}

uvm_ml_packer_int::~uvm_ml_packer_int() { 
  delete m_rep_int;
}

void uvm_ml_packer_int::reset() { m_rep_int->reset(); }

bool uvm_ml_packer_int::use_metadata() const {
  return m_rep_int->use_metadata();
}

void uvm_ml_packer_int::use_metadata(bool b) {
  if (!b) {
    cerr << "WARNING: uvm_ml_packer_int use_metadata must be true. " 
      << "Ignoring attempt to set it to false" << endl;
    return;
  }
}

int uvm_ml_packer_int::get_remaining_unpacked_bits() {
  return m_rep_int->get_remaining_unpacked_bits();
}

void uvm_ml_packer_int::set_bits(unsigned* bits, unsigned nbits) {
  m_rep_int->set_bits(bits, nbits);
}

////////

uvm_ml_packer_int& uvm_ml_packer_int::operator << (bool a) { 
  int i = a ? 1 : 0;
  pack_unsigned(i, m_rep_int);
  return *this;
}

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (bool& a) { 
  unsigned aa;
  unpack_unsigned(aa, m_rep_int); 
  if (aa == 0)
    a = false;
  else
    a = true;
  return *this;
}

/////////////////////////////

#define def_int_pack_int_operators(T) \
uvm_ml_packer_int& uvm_ml_packer_int::operator << (T a) { \
  pack_unsigned(a, m_rep_int);\
  return *this;\
} \
uvm_ml_packer_int& uvm_ml_packer_int::operator >> (T& a) {  \
  unpack_unsigned(a, m_rep_int); \
  return *this; \
}

typedef unsigned char uchar;
typedef unsigned short ushort;
typedef unsigned int uint;
typedef unsigned long ulong;

uvm_ml_packer_int& uvm_ml_packer_int::operator << (char a) { 
  pack_unsigned(int(a), m_rep_int);
  return *this;
} 

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (char& a) {  
  unsigned aa;
  unpack_unsigned(aa, m_rep_int); 
  a = char(aa); 
  return *this; 
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (short a) { 
  pack_unsigned(int(a), m_rep_int);
  return *this;
} 

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (short& a) {  
  unsigned aa;
  unpack_unsigned(aa, m_rep_int); 
  a = short(aa); 
  return *this; 
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (unsigned char a) { 
  pack_unsigned(unsigned(a), m_rep_int);
  return *this;
} 

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (unsigned char& a) {  
  unsigned aa;
  unpack_unsigned(aa, m_rep_int); 
  a = (unsigned char)(aa); 
  return *this; 
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (unsigned short a) { 
  pack_unsigned(unsigned(a), m_rep_int);
  return *this;
} 

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (unsigned short& a) {  
  unsigned aa;
  unpack_unsigned(aa, m_rep_int); 
  a = (unsigned short)(aa); 
  return *this; 
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (uint64 a) { 
#if defined(_AIX) || defined(sparc)
  // swap the two bytes before packing
  unsigned u[2];
  memcpy(u, &a, 8);
  unsigned tmp = u[0];
  u[0] = u[1];
  u[1] = tmp;
  memcpy(&a, u, 8); 
#endif
  pack_unsigned(a, m_rep_int);
  return *this;
} 

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (uint64& a) {  
  unpack_unsigned(a, m_rep_int); 
#if defined(_AIX) || defined(sparc)
  // the 2 words are swapped
  unsigned u[2];
  memcpy(u, &a, 8);
  unsigned tmp = u[0];
  u[0] = u[1];
  u[1] = tmp;
  memcpy(&a, u, 8);
#endif
  return *this; 
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (int64 a) { 
#if defined(_AIX) || defined(sparc)
  // swap the two bytes before packing
  int u[2];
  memcpy(u, &a, 8);
  int tmp = u[0];
  u[0] = u[1];
  u[1] = tmp;
  memcpy(&a, u, 8); 
#endif
  pack_unsigned(a, m_rep_int);
  return *this;
} 

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (int64& a) {  
  unpack_unsigned(a, m_rep_int); 
#if defined(_AIX) || defined(sparc)
  // the 2 words are swapped
  int u[2];
  memcpy(u, &a, 8);
  int tmp = u[0];
  u[0] = u[1];
  u[1] = tmp;
  memcpy(&a, u, 8);
#endif
  return *this; 
}
def_int_pack_int_operators(int)
def_int_pack_int_operators(uint)
def_int_pack_int_operators(long)
def_int_pack_int_operators(ulong)

////////////////////////////////////

uvm_ml_packer_int& uvm_ml_packer_int::operator << (const char* a) { 
  if (!a) {
    m_rep_int->pack_string("");
  } else {
    m_rep_int->pack_string(a);
  }
  return *this;
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (std::string a) { 
  m_rep_int->pack_string(a);
  return *this;
}

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (std::string& a) { 
  m_rep_int->unpack_string(a);
  return *this;
}

void uvm_ml_packer_int::pack_obj_header(const std::string & type_name) {
  m_rep_int->pack_obj_header(type_name);
}

void uvm_ml_packer_int::pack_null() {
  m_rep_int->pack_null();
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (uvm_object* a) {
  m_rep_int->pack_obj(a);
  return *this;
}

void * uvm_ml_packer_int::unpack_obj_header() {
  return m_rep_int->unpack_obj_header();
}

uvm_object * uvm_ml_packer_int::unpack_uvm_obj_header() {
  return m_rep_int->unpack_uvm_obj_header();
}

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (uvm_object*& a) {
  m_rep_int->unpack_obj(a);
  return *this;
}

uvm_ml_packer_int& uvm_ml_packer_int::operator << (const uvm_object& a) {
  m_rep_int->pack_obj((uvm_object*)(&a));
  return *this;
}

#define def_int_pack_sctype_operators(T) \
uvm_ml_packer_int& uvm_ml_packer_int::operator << (const T& a) { \
  m_rep_int->pack_##T(a);\
  return *this;\
} \
uvm_ml_packer_int& uvm_ml_packer_int::operator >> (T& a) {  \
  m_rep_int->unpack_##T(a); \
  return *this; \
}

def_int_pack_sctype_operators(sc_logic)
def_int_pack_sctype_operators(sc_bv_base)
def_int_pack_sctype_operators(sc_lv_base)
def_int_pack_sctype_operators(sc_int_base)
def_int_pack_sctype_operators(sc_uint_base)
def_int_pack_sctype_operators(sc_signed)
def_int_pack_sctype_operators(sc_unsigned)

//template <> 
uvm_ml_packer_int& uvm_ml_packer_int::operator << (const std::vector<bool>& a) {
  // first pack the size of the vector before packing its elements
  unsigned nbits = a.size();
  (*this) << nbits;

  // the bits need to be packed tightly in orer to map to
  // dynamic bit vector in SV or to list of bits in e. So
  // cannot pack each bit individually - instead map to
  // sc_bv and then pack sc_bv atomically
 
  if (nbits == 0) 
    return *this;

  sc_bv_base bv((int)nbits);
  for (unsigned i = 0; i < nbits; i++) {
  bv[i] = a[i];
  }
  (*this) << bv;
  return *this;
}

uvm_ml_packer_int& uvm_ml_packer_int::operator >> (std::vector<bool>& a) {
  a.clear();
  unsigned nbits;
  // first unpack the size of the vector before unpacking its elements
  (*this) >> nbits;

  // the bits need to be unpacked tightly in orer to map from
  // dynamic bit vector in SV or from list of bits in e. So
  // cannot unpack each bit individually - instead unpack to
  // sc_bv atomically and then map from sc_bv

  if (nbits == 0)
    return *this;
 
  sc_bv_base bv((int)nbits);
  (*this) >> bv;
  for (unsigned i = 0; i < nbits; i++) {
    bool b;
    b = bv[i].to_bool();
    a.push_back(b);
  }
  return *this;
}

//////////


void uvm_ml_packer_int::set_from_uvm_ml_packed_obj(uvm_ml_packed_obj* v) {
  set_bits(v->val, v->size);
}

void uvm_ml_packer_int::fill_uvm_ml_packed_obj(uvm_ml_packed_obj* v) {
  int nwords = m_rep_int->get_pack_index(); 
  v->size = nwords * 32;
  unsigned* bv = m_rep_int->get_packed_bits();

  // this mlupo is going over to the backplane and then onto the SV adaptor;
  // the SV adaptor is hardcoded to accept the max bits, hence allocate
  // max words here
  static int alloc_words = uvm_ml::uvm_ml_utils::get_max_words();
  
  uvm_ml_packed_obj::allocate(v, alloc_words); 
  memcpy(v->val, bv, nwords*sizeof(unsigned));
}


} // namespace uvm 

