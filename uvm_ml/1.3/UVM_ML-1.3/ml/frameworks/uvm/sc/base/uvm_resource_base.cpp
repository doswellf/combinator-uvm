//----------------------------------------------------------------------
//   Copyright 2013 Advanced Micro Devices Inc.
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

#include "uvm_resource_base.h"
#include "uvm_globals.h"
#include "uvm_resource_pool.h"
#include <packages/boost/include/regex.hpp>


namespace uvm {

unsigned int uvm_resource_base::m_default_precedence = 1000;

//----------------------------------------------------------------------
//! Constructor
/*!
 *  @param name  - Name of resource
 *  @param scope - Resource scope
 *
 */
uvm_resource_base::uvm_resource_base(const std::string& name, const std::string& scope) :
    sc_object(),
    m_read_only(false),
    m_precedence(m_default_precedence),
    m_name(name)
{
    set_scope(scope);
}

//----------------------------------------------------------------------
//! Desstructor
//
uvm_resource_base::~uvm_resource_base()
{
}

//----------------------------------------------------------------------
//! Set the resource to be read-only.
//
void uvm_resource_base::set_read_only()
{
    m_read_only = true;
}

//----------------------------------------------------------------------
//! Set the resource to be read and write
//
void uvm_resource_base::set_read_write()
{
    m_read_only = false;
}

//----------------------------------------------------------------------
//! Query the read-write attribute of the resource.
/*!
 *  @return read-write status
 *      - false : writable
 *      - true : read only
 */
bool uvm_resource_base::is_read_only()
{
    return m_read_only;
}

//----------------------------------------------------------------------
//! Wait until the resource has been modified.
//
void uvm_resource_base::wait_modified()
{
    ::sc_core::wait(m_modified_event);
}

//----------------------------------------------------------------------
//! Set scope for the resource
/*!
 *  @param scope - Scope to set for this resource
 */
void uvm_resource_base::set_scope(std::string scope)
{
    m_scope = uvm_glob_to_regex(scope);
}

//----------------------------------------------------------------------
//! Return the scope for the resource
/*!
 *  @return Scope
 */
std::string uvm_resource_base::get_scope()
{
    return m_scope;
}

//----------------------------------------------------------------------
//! Determine if the resource is visible in the given scope.
/*!
 *  @param scope - Scope to check
 * 
 *  @return status
 *     - 0 : Resource not visible in given scope 
 *     - 1 : Resource is visible in givin scope
 */
bool uvm_resource_base::match_scope(std::string scope)
{
    uvmsc_boost::smatch what;
    uvmsc_boost::regex  re(m_scope);

    return uvmsc_boost::regex_match((const std::string) scope, what, re);
}


//----------------------------------------------------------------------
//! Set the precedence of this resource.
/*!
 *  @param precedence
 */
void uvm_resource_base::set_precedence(unsigned int precedence)
{
    m_precedence = precedence;
}


//----------------------------------------------------------------------
//! Return the precedence of this resource.
/*!
 *  @return Precedence
 */
unsigned int uvm_resource_base::get_precedence()
{
    return m_precedence;
}

//----------------------------------------------------------------------
//! Set the priority of this resource in the pool.
/*! PRI_HIGH - move to front of pool.
 *  PRI_LOW  - move to back of pool.
 *  @param priority
 */
void uvm_resource_base::set_priority(uvm_resource_priority_e priority)
{
    uvm_resource_pool * rpool = uvm_resource_pool::get();
    rpool->set_priority_name(this, priority);
}


//----------------------------------------------------------------------
//! Convert the resource value to string.
/*!
 *  Should be implemented in specialization class.  Base class does
 *  not know how to convert the value so return "?".
 *
 *  @return String respresentation of resource value.
 */
std::string uvm_resource_base::convert2string()
{
    return "?";
}

//----------------------------------------------------------------------
//! Return the name of the resource.
/*!
 *  @return Name of the resource
 */
std::string uvm_resource_base::get_name()
{
    return m_name;
}


}  // namespace
