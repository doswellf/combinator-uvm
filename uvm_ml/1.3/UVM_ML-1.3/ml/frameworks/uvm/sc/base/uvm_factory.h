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

/*! \file uvm_factory.h
  \brief Factory for UVM-SC objects.
*/

#ifndef UVM_FACTORY_H
#define UVM_FACTORY_H

#include "base/uvm_ids.h"

#include <string>
#include <iostream>

//////////////////////

namespace uvm {

//////////////////////

// forward declarartions of necessary classes

class uvm_object;
class uvm_component;
class uvm_factory_rep;
class uvm_object_creator;
class uvm_component_creator;

//////////////////////

//------------------------------------------------------------------------------
//
// CLASS: uvm_creator
//
// Provides the interface used for registering proxy classes with the
// factory which is necessary for creating such proxy classes from 
// the factory.
// The two different kinds of classes that are supported by the factory
// are uvm_component and uvm_object.
//
//------------------------------------------------------------------------------

/*! \class uvm_creator
  \brief Provides the interface used for registering proxy classes with the factory.

  The two different kinds of classes that are supported by the factory are uvm_component and uvm_object
*/
class uvm_creator {
public:
  virtual ~uvm_creator();
  virtual void *                 create_class(const std::string& name = "") = 0;
  virtual uvm_object_creator*    as_object_creator();
  virtual uvm_component_creator* as_component_creator();
protected:
  uvm_creator();
};

//------------------------------------------------------------------------------
//
// CLASS: uvm_object_creator
//
// Implements the interface used by the factory to create an uvm_object.
// Derives from uvm_creator.
// Usually, the UVM_OBJECT_UTILS macro in an uvm_object defines the
// corresponding uvm_object_creator class. 
//
//------------------------------------------------------------------------------

/*! \class uvm_object_creator
  \brief Implements the interface used by the factory to create an uvm_object.

  Usually, the UVM_OBJECT_UTILS macro in an uvm_object defines the corresponding uvm_object_creator class
*/
class uvm_object_creator : public uvm_creator {
public:
  uvm_object_creator();
  virtual uvm_object* create(
    const std::string& name = ""
  ) = 0;
  virtual void * create_class(const std::string& name = "") { return create(name); }
  virtual ~uvm_object_creator();
  virtual uvm_object_creator* as_object_creator();
};

//------------------------------------------------------------------------------
//
// CLASS: uvm_component_creator
//
// Implements the interface used by the factory to create an uvm_component.
// Derives from uvm_creator.
// Usually, the UVM_COMPONENT_UTILS macro in an uvm_object defines the
// corresponding uvm_component_creator class. 
//
//------------------------------------------------------------------------------

/*! \class uvm_component_creator
  \brief Implements the interface used by the factory to create an uvm_component.

  Usually, the UVM_COMPONENT_UTILS macro in an uvm_object defines the corresponding uvm_component_creator class. 
*/
class uvm_component_creator : public uvm_creator {
public:
  uvm_component_creator();
  virtual uvm_component* create(
    const std::string& name = ""
  ) = 0;
  virtual void * create_class(const std::string& name = "") { return create(name); }
  virtual ~uvm_component_creator();
  virtual uvm_component_creator* as_component_creator();
};

//////////////////////

//------------------------------------------------------------------------------
//
// CLASS: uvm_factory
//
// Class for creating uvm_objects and uvm_components. 
// Before creation, the factory processes any overrides, if applicable. 
// Class types  have to be registered with the factory using the 
// uvm_creator class.
// A singleton factory instance is created for a given simulation run.
//
//------------------------------------------------------------------------------

/*! \class uvm_factory
  \brief Class for creating uvm_objects and uvm_components.

  Before creation, the factory processes any overrides, if applicable. Class types  have to be registered with the factory using the uvm_creator class. A singleton factory instance is created for a given simulation run
*/
class uvm_factory {
public:

  //----------------------------------------------------------------------------
  // Register an object or a component with the factory. 
  //
  // Usually, the UVM_OBJECT_REGISTER and UVM_COMPONENT_REGISTER macros 
  // will invoke these factory member methods to register a particular 
  // object or component with the factory.
  //----------------------------------------------------------------------------

  static int register_class_creator(
    const std::string & type_name, 
    uvm_creator* creator
  );
  static int register_uvm_object_creator(
    const std::string & type_name, 
    uvm_object_creator* creator
  );
  static int register_component_creator(
    const std::string & type_name, 
    uvm_component_creator* creator
  );
  
  //----------------------------------------------------------------------------
  // Create an uvm_object or an uvm_component through the factory.
  //
  // Overrides are applied before creation.
  //----------------------------------------------------------------------------

  static uvm_object* create_uvm_object(
    std::string type_name,
    std::string inst_path = "",
    std::string name = "",
    bool no_overrides = false
  );
  static uvm_component* create_component(
    std::string type_name,
    std::string inst_path = "",
    std::string name = ""
  );
  static void* create_registered_class(
    const std::string & type_name
  );

  //----------------------------------------------------------------------------
  // Set up type overrides or instance overrides through the factory.
  //
  // Wildcards('*' and '?') are allowed in "inst_path" of instance overrides.
  // Instance overrides have precedence over type overrides.
  //----------------------------------------------------------------------------

  static void set_type_override(
    std::string orignal_type_name,
    std::string replacement_type_name,
    bool replace = true
  );
  static void set_inst_override(
    std::string inst_path,
    std::string orignal_type_name,
    std::string replacement_type_name
  );

  //----------------------------------------------------------------------------
  // Print all overrides in the factory.
  //
  // Useful for debugging purposes.
  //----------------------------------------------------------------------------

  static void print_all_overrides(); // for debugging use

  // methods primarily for internal use

  static std::string get_type_override(
    std::string orignal_type_name
  );
  static std::string get_inst_override(
    std::string inst_path,
    std::string orignal_type_name
  );
  //
  static bool is_component_registered(const std::string & type_name);
  static bool is_uvm_object_registered(const std::string & type_name);
  static bool is_class_registered(const std::string & type_name);
protected:
  static uvm_factory_rep* m_rep; // internal implementation class
};

//////////////////////

} // namespace uvm

//////////////////////

#endif
