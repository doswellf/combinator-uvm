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

#include "base/uvm_resource_pool.h"
#include "base/uvm_resource_base.h"
#include "base/uvm_globals.h"
#include <algorithm>
#include <packages/boost/include/regex.hpp>


namespace uvm {

uvm_resource_pool* uvm_resource_pool::m_pool = NULL;

//----------------------------------------------------------------------
//! Constructor
//
uvm_resource_pool::uvm_resource_pool()
{
}

//----------------------------------------------------------------------
//! Desstructor
//
uvm_resource_pool::~uvm_resource_pool()
{
    std::map<std::string, resource_q*>::iterator it;


    for (it = m_resource_q_map.begin(); it != m_resource_q_map.end(); it++)
    {
        for (int i = 0; i < it->second->size(); i++)
        {
            if ((*it->second)[i] != NULL)
                delete (*it->second)[i];
        }
        it->second->clear();
    }
    m_resource_q_map.clear();
}

//----------------------------------------------------------------------
//! Returns the singleton to the resource pool
/*!
 *  @return Singleton to the resource pool
 */
uvm_resource_pool* uvm_resource_pool::get()
{
    if (m_pool == NULL)
        m_pool = new uvm_resource_pool();

    return m_pool;
}


//----------------------------------------------------------------------
//! Add resource into pool.
/*!
 *  @param rsrc     - Pointer to resource to be added.
 *  @param override - Resource will be added into the back of the pool
 *                    unless override is set to 1
 */
void uvm_resource_pool::set(uvm_resource_base* rsrc, bool override)
{
    std::string name   = rsrc->get_name();
    resource_q* rsrc_q = NULL;
    std::map<std::string, resource_q*>::iterator it_map;
    resource_q::iterator it_q;

    it_map = m_resource_q_map.find(name);
    if (it_map != m_resource_q_map.end())
        rsrc_q = it_map->second;
    else
        rsrc_q = new resource_q();

    it_q = std::find(rsrc_q->begin(), rsrc_q->end(), rsrc);
    if (it_q != rsrc_q->end())
        rsrc_q->erase(it_q);

    if (override)
        rsrc_q->push_front(rsrc);
    else
        rsrc_q->push_back(rsrc);

    m_resource_q_map[name] = rsrc_q;
}

//----------------------------------------------------------------------
//! Move the resource to the front of the pool.
/*!
 *  @param rsrc - Pointer to resource to be moved.
 */
void uvm_resource_pool::set_override(uvm_resource_base* rsrc)
{
    set(rsrc, true);
}

//----------------------------------------------------------------------
//! Find the highest precedence resource
/*! with the specified name in the the specified scope.
 *
 *  @param scope   - Scope of the resource
 *  @param name    - Name of the resource
 *  @param type_id - Type ID of resource to get
 *
 *  @return Pointer to the resource if found, otherwise NULL.
 */
uvm_resource_base* uvm_resource_pool::get_by_name(const std::string& scope, const std::string& name, const std::type_info& type_id)
{
    resource_q rsrc_q = lookup_name(scope, name, type_id); 
    return get_highest_precedence(rsrc_q);    
}

//----------------------------------------------------------------------
//! Find the highest precedence resource with regex name in the 
/*! the specified scope.
 *
 *  @param scope   - Scope of the resource
 *  @param name    - Name of the resource (regex)
 *  @param type_id - Type ID of resource to get
 *
 *  @return Pointer to the resource if found, otherwise NULL.
 */
uvm_resource_base* uvm_resource_pool::get_by_name_regex(const std::string& scope, const std::string& name, const std::type_info& type_id)
{
    resource_q rsrc_q = lookup_regex(scope, name, type_id); 
    return get_highest_precedence(rsrc_q);    
}


//----------------------------------------------------------------------
//! Lookup of the resources with the specified name, scope and type
/*! 
 *  @param scope   - Scope of the resource
 *  @param name    - Name of resource
 *  @param type_id - Type ID of the resource
 *
 *  @return Queue of resources matching search conditions.
 */
resource_q uvm_resource_pool::lookup_name(const std::string& scope, const std::string& name, const std::type_info& type_id)
{
    resource_q *        rsrc_q; 
    resource_q          rsrc_result_q; 
    uvmsc_boost::smatch what;
    uvmsc_boost::regex  re(uvm_glob_to_regex(name));

    std::map<std::string, resource_q*>::iterator it;

    it = m_resource_q_map.find(name);
    if (it != m_resource_q_map.end())
    {
        rsrc_q = it->second;
        for (int i = 0; i < rsrc_q->size(); i++)
        {
            if ( (*rsrc_q)[i]->match_scope(scope) && (typeid((*rsrc_q)[i]) == type_id) )
                rsrc_result_q.push_back((*rsrc_q)[i]);
        }
    }

    return rsrc_result_q;
}

//----------------------------------------------------------------------
//! Lookup of the resources in the specified scope and type.
/*! Both name could be a regular expression.
 *
 *  @param scope   - Scope of the resource
 *  @param name    - Name of resource
 *  @param type_id - Type ID of the resource
 *
 *  @return Queue of resources matching search conditions.
 */
resource_q uvm_resource_pool::lookup_regex(const std::string& scope, const std::string& name, const std::type_info& type_id)
{
    resource_q          rsrc_q; 
    uvmsc_boost::smatch what;
    uvmsc_boost::regex  re(uvm_glob_to_regex(name));

    std::map<std::string, resource_q*>::iterator it;

    for (it = m_resource_q_map.begin(); it != m_resource_q_map.end(); it++)
    {
        int j = 0;
        if (uvmsc_boost::regex_match((const std::string) it->first, what, re))
        {
            for (int i = 0; i < it->second->size(); i++)
            {
                if ( (*it->second)[i]->match_scope(scope) && (((*it->second)[i])->get_value_type_id() == type_id) )
                    rsrc_q.push_back((*it->second)[i]);
            }
        }
        j++;
    }

    return rsrc_q;
}

//----------------------------------------------------------------------
//! Find all resources in the specified scope.
/*!
 *  @param scope - Scope of the resource
 *
 *  @return Queue of resources matching search condition.
 */
resource_q uvm_resource_pool::lookup_scope(const std::string& scope)
{
    resource_q   rsrc_result_q; 

    std::map<std::string, resource_q*>::iterator it;
    for (it = m_resource_q_map.begin(); it != m_resource_q_map.end(); it++)
    {
        for (int i = 0; i < it->second->size(); i++)
        {
            if ((*it->second)[i]->match_scope(scope))
                rsrc_result_q.push_back((*it->second)[i]);
        }
    }

    return rsrc_result_q;
}

//----------------------------------------------------------------------
//! Return the highest precedence resrouce in the resource queue.
/*!
 *  @param rsrc_q - Queue of resources
 *
 *  @return Pointer to the highest precedence resource
 */
uvm_resource_base* uvm_resource_pool::get_highest_precedence(resource_q& rsrc_q)
{
    uvm_resource_base * rsrc = NULL;
    unsigned int precedence;

    if (rsrc_q.size() > 0)
    {
        precedence = rsrc_q[0]->get_precedence();
        rsrc       = rsrc_q[0];
        for (int i = 1; i < rsrc_q.size(); i++)
        {
            if (rsrc_q[i]->get_precedence() > precedence)
            {
                precedence = rsrc_q[i]->get_precedence();
                rsrc       = rsrc_q[i];
            }
        }
    }

    return rsrc;
}

//----------------------------------------------------------------------
//! Sort the resource queue by precedence
/*!
 *  @param rsrc_q - Reference to queue of resources to be sorted
 *
 */
void uvm_resource_pool::sort_by_precedence(resource_q& rsrc_q)
{
    std::sort(rsrc_q.begin(), rsrc_q.end(), &uvm_resource_pool::rsrc_prec_compare);
}

//----------------------------------------------------------------------
//! Resource precedence comparison.
/*!
 *  @param rsrc1 - Pointer to resource 1
 *  @param rsrc2 - Pointer to resource 2
 *
 *  @return Result of comparison:
 *      - true  : Precedence of rsrc1 is greater than 2
 *      - false : Precedence of rsrc1 is less than 2
 */
bool uvm_resource_pool::rsrc_prec_compare(uvm_resource_base * rsrc1, uvm_resource_base * rsrc2)
{
    if (rsrc1 == NULL)
        return false;

    if (rsrc2 == NULL)
        return true;

    return (rsrc1->get_precedence() > rsrc2->get_precedence()); 
}

//----------------------------------------------------------------------
//! Move the resource to the front or the back of the queue depending on
/*! the priority.
 *
 *  @param rsrc     - Pointer to the resource
 *  @param rsrc_q   - Queue of resources
 *  @param priority - Priority for the resource
 *
 */
void uvm_resource_pool::set_priority_queue (
    uvm_resource_base*       rsrc,
    resource_q &             rsrc_q,
    uvm_resource_priority_e  priority
)
{
    resource_q::iterator it;
    it = std::find(rsrc_q.begin(), rsrc_q.end(), rsrc);

    if (it != rsrc_q.end())
    {
        rsrc_q.erase(it);
        if (priority == PRI_HIGH)
            rsrc_q.push_front(rsrc);
        else
            rsrc_q.push_back(rsrc);
    }
    else
    {
        std::cout << "WARNING: uvm_resource_pool::set_priority_queue() Resource not found int queue" << std::endl;
    }
}


//----------------------------------------------------------------------
//! Set priority for the resource in the pool.
/*!
 *  @param rsrc     - Pointer to the resource
 *  @param priority - Priority for the resource
 *
 */
void uvm_resource_pool::set_priority_name(uvm_resource_base* rsrc, uvm_resource_priority_e priority)
{
    resource_q* rsrc_q = NULL;

    rsrc_q = m_resource_q_map[rsrc->get_name()];
    if (rsrc_q != NULL)
    {
        set_priority_queue(rsrc, (*rsrc_q), priority);
    }
    else
    {
        std::cout << "WARNING: uvm_resource_pool::set_priority_name resource name not found in pool" << std::endl;
    }
}

}   // namspace




