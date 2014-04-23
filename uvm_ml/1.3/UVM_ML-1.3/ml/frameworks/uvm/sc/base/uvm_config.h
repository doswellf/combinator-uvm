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

/*! \file uvm_config.h
  \brief Base class for UVM-SC configuration object.
*/

#ifndef UVM_CONFIG_H
#define UVM_CONFIG_H

#include "sysc/datatypes/bit/sc_lv.h"

#include <string>

//////////////

namespace uvm {

//------------------------------------------------------------------------------
//
// Internal implementation classes for configuration.
//
//------------------------------------------------------------------------------


// forward declaration of necessary classes.

class uvm_object;
class uvm_component;

class uvm_config_item_int;
class uvm_config_item_string;
class uvm_config_item_object;

typedef enum { 
  uvm_config_type_int, 
  uvm_config_type_string, 
  uvm_config_type_object 
} uvm_config_type;

////////////

//------------------------------------------------------------------------------
//
// CLASS: uvm_config_item
//
// Internal implementation class.
// Base class to represent a configuration setting.
//------------------------------------------------------------------------------

/*! \class uvm_config_item
  \brief Base class to represent a configuration setting.

  
*/
class uvm_config_item {
public:
  friend class uvm_config;
  friend class uvm_config_mgr;
  friend class uvm_factory_rep;
  uvm_config_item(
    const std::string& instname,
    const std::string& field,
    uvm_component* inst_set_by,
    uvm_config_type type
  );
  virtual ~uvm_config_item();
  virtual uvm_config_item_int* as_int();
  virtual uvm_config_item_string* as_string();
  virtual uvm_config_item_object* as_object();
  virtual void print() const = 0;
  void print_match(
    uvm_component* inst_getting,
    std::string instname_req,
    std::string field_req
  ) const;
protected:
  uvm_config_type m_type;
  std::string m_instname;
  std::string m_field;
  uvm_component* m_inst_set_by;
};

//------------------------------------------------------------------------------
//
// CLASS: uvm_config_item_int
//
// Internal implementation class.
// Represents a configuration setting specified by set_config_int().
// Stores the specified value as a sc_lv<4096>.
//------------------------------------------------------------------------------

/*! \class uvm_config_item_int
  \brief Represents a configuration setting specified by set_config_int().

  Stores the specified value as a sc_lv<4096>.
*/
class uvm_config_item_int : public uvm_config_item {
public:
  uvm_config_item_int(
    const std::string& instname,
    const std::string& field,
    uvm_component* inst_set_by,
    sc_dt::sc_lv<4096> val
  );
  virtual ~uvm_config_item_int();
  virtual uvm_config_item_int* as_int();
  sc_dt::sc_lv<4096> value() const;
  virtual void print() const;
protected:
  sc_dt::sc_lv<4096> m_val;
};

//------------------------------------------------------------------------------
//
// CLASS: uvm_config_item_string
//
// Internal implementation class.
// Represents a configuration setting specified by set_config_string().
//------------------------------------------------------------------------------

/*! \class uvm_config_item_string
  \brief Represents a configuration setting specified by set_config_string().

  
*/
class uvm_config_item_string : public uvm_config_item {
public:
  uvm_config_item_string(
    const std::string& instname,
    const std::string& field,
    uvm_component* inst_set_by,
    const std::string& val
  );
  ~uvm_config_item_string();
  virtual uvm_config_item_string* as_string();
  std::string value() const;
  virtual void print() const;
protected:
  std::string m_val;
};

//------------------------------------------------------------------------------
//
// CLASS: uvm_config_item_object
//
// Internal implementation class.
// Represents a configuration setting specified by set_config_object().
//------------------------------------------------------------------------------

/*! \class uvm_config_item_object
  \brief Represents a configuration setting specified by set_config_object().

  
*/
class uvm_config_item_object : public uvm_config_item {
public:
  uvm_config_item_object(
    const std::string& instname,
    const std::string& field,
    uvm_component* inst_set_by,
    uvm_object* val
  );
  ~uvm_config_item_object();
  virtual uvm_config_item_object* as_object();
  uvm_object* value() const;
  virtual void print() const;
protected:
  uvm_object* m_val;
};

/////////////////////

typedef std::vector<uvm_config_item*> uvm_config_item_vector;

//------------------------------------------------------------------------------
//
// CLASS: uvm_config
//
// Internal implementation class.
// Represents a table of configuration settings specified inside an 
// uvm_component or at the global level. 
//------------------------------------------------------------------------------

/*! \class uvm_config
  \brief Represents a table of configuration settings specified inside a uvm_component or at the global level.

  
*/
class uvm_config {
public:
  friend class uvm_factory_rep;
  uvm_config();
  ~uvm_config();
  void add_config_item(uvm_config_item* item);
  uvm_config_item* get_config_item(
    uvm_config_type type,
    const std::string& instname, 
    const std::string& field
  );
private:  
  uvm_config_item_vector m_vec;
};

/////////

typedef std::vector<uvm_config*> uvm_config_stack;

//------------------------------------------------------------------------------
//
// CLASS: uvm_config_mgr
//
// Internal implementation class.
// Stores the  configuration table for global configuration settings.
// Implements the global configuration interface and the configuration
// interface in uvm_component.
// 
//------------------------------------------------------------------------------

/*! \class uvm_config_mgr
  \brief Stores the  configuration table for global configuration settings.

  Implements the global configuration interface and the configuration interface in uvm_component
*/
class uvm_config_mgr {
public:
  friend class uvm_component;
  //
  uvm_config_mgr();
  ~uvm_config_mgr();
  //
  // set/get routines for the global config table
  //
  bool print_config_matches() const;
  void print_config_matches(bool b);

  uvm_config* global_config();
  template <typename T> void set_config_int(
    const std::string& instname,
    const std::string& field,
    const T& val
  );
  void set_config_string(
    const std::string& instname,
    const std::string& field,
    const std::string& val
  );
  void set_config_object(
    const std::string& instname,
    const std::string& field,
    uvm_object* val,
    bool clone = true
  );
  template <class T> bool get_config_int(
    const std::string& instname,
    const std::string& field,
    T& val
  );
  bool get_config_string(
    const std::string& instname,
    const std::string& field,
    std::string& val
  );
  bool get_config_object(
    const std::string& instname,
    const std::string& field,
    uvm_object*& val,
    bool clone = true
  );
public: // for internal use
  template <typename T> void set_config_int(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    const T& val
  );
  void set_config_int(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    const sc_dt::sc_lv<4096>& val
  );
  void set_config_string(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    const std::string& val
  );
  void set_config_object(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    uvm_object* val,
    bool clone
  );
private:
  template <class T> bool get_config_int(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    T& val
  );
  uvm_config_item_int* get_config_int_internal(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    sc_dt::sc_lv<4096>& val
  );
  uvm_config_item_string* get_config_string(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    std::string& val
  );
  uvm_config_item_object* get_config_object(
    uvm_component* inst,
    const std::string& instname,
    const std::string& field,
    uvm_object*& val,
    bool clone = true
  );
  //
  void set_config_item(
    uvm_component* inst,
    uvm_config_item* item
  );
  uvm_config_item* get_config_item(
    uvm_config_type type,    
    uvm_component* inst,
    const std::string& instname,
    const std::string& field
  );
  //
private:
  uvm_config* m_global_config;
  bool m_print_config_matches;
};

uvm_config_mgr* uvm_get_config_mgr();

/////////////

//------------------------------------------------------------------------------
// Templated functions necessary to support get_config_int()
//
//------------------------------------------------------------------------------

template <typename T> void uvm_convert_from_lv(T& v, sc_dt::sc_lv<4096> lv) {
  v = lv; 
}
inline void uvm_convert_from_lv(sc_dt::sc_logic& v, const sc_dt::sc_lv<4096>& lv) { \
  v = lv.get_bit(0);
}
#define uvm_convert_from_lv_int_type(t) \
inline void uvm_convert_from_lv(t& v, const sc_dt::sc_lv<4096>& lv) { \
  sc_dt::uint64 u = lv.to_uint64(); \
  v = u;  \
}
uvm_convert_from_lv_int_type(bool)
uvm_convert_from_lv_int_type(char)
uvm_convert_from_lv_int_type(sc_dt::uchar)
uvm_convert_from_lv_int_type(short)
uvm_convert_from_lv_int_type(ushort)
uvm_convert_from_lv_int_type(int)
uvm_convert_from_lv_int_type(uint)
uvm_convert_from_lv_int_type(long)
uvm_convert_from_lv_int_type(ulong)
uvm_convert_from_lv_int_type(sc_dt::int64)
uvm_convert_from_lv_int_type(sc_dt::uint64)
// and similarly for char, unsigned, ...

/////////////

//------------------------------------------------------------------------------
// Templated functions necessary to support set_config_int()
//
//------------------------------------------------------------------------------

template <typename T> sc_dt::sc_lv<4096> uvm_convert_to_lv(const T& v) {
  sc_dt::sc_lv<4096> lv = v;
  return lv;
}
inline sc_dt::sc_lv<4096> uvm_convert_to_lv(const sc_dt::sc_logic& v) {
  sc_dt::sc_lv<4096> lv = 0;
  lv.set_bit(0,v.value());
  return lv;
}

/////////////

//------------------------------------------------------------------------------
// Implementation of templated functions set_config_int() and get_config_int()
//
//------------------------------------------------------------------------------

template <typename T> void uvm_config_mgr::set_config_int(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  const T& val
) {
  sc_dt::sc_lv<4096> lv = uvm_convert_to_lv(val);
  set_config_int(inst,instname,field,lv);
}

template <typename T> void uvm_config_mgr::set_config_int(
  const std::string& instname,
  const std::string& field,
  const T& val
) {
  set_config_int(0,instname,field,val);
}

template <typename T> bool uvm_config_mgr::get_config_int(
  uvm_component* inst,
  const std::string& instname,
  const std::string& field,
  T& val
) {
  sc_dt::sc_lv<4096> lv;
  uvm_config_item_int* b = get_config_int_internal(inst,instname,field,lv);
  if (!b) {
    return false;
  }
  uvm_convert_from_lv(val,lv);
  if (print_config_matches()) {
    b->print_match(inst,instname,field);
    std::cout << "Value: " << val << std::endl;
  }
  return b;
}

template <typename T> bool uvm_config_mgr::get_config_int(
  const std::string& instname,
  const std::string& field,
  T& val
) {
  return get_config_int(0,instname,field,val);
}

/////////////

} // namespace uvm

#endif
