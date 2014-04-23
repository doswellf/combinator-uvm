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

/*! @file uvm_resource_pool.h
 *  Header file for UVM-SC resource_base pool
 */

#ifndef UVM_RESOURCE_POOL_H
#define UVM_RESOURCE_POOL_H

#include <map>
#include <deque>
#include <string>
#include  "base/uvm_resource_base.h"


namespace uvm {


typedef std::deque<uvm_resource_base*> resource_q; 


class uvm_resource_pool
{
public:

    uvm_resource_pool();
    ~uvm_resource_pool();

    static uvm_resource_pool* get();



    void set(uvm_resource_base* rsrc, bool override = false);
    void set_override(uvm_resource_base* rsrc);

    uvm_resource_base* get_by_name(const std::string& scope, const std::string& name, const std::type_info& type_id);
    uvm_resource_base* get_by_name_regex(const std::string& scope, const std::string& name, const std::type_info& type_id);
    resource_q lookup_name(const std::string& scope, const std::string& name, const std::type_info& type_id);
    resource_q lookup_regex(const std::string& scope, const std::string& name, const std::type_info& type_id);
    resource_q lookup_scope(const std::string& scope);

    uvm_resource_base* get_highest_precedence(resource_q& rsrc_q);
    void sort_by_precedence(resource_q& rsrc_q);

    void set_priority_queue(uvm_resource_base*      rsrc,
                            resource_q &            rsrc_q,
                            uvm_resource_priority_e priority);


    void set_priority_name(uvm_resource_base* rsrc,
                           uvm_resource_priority_e priority);



private:

    static bool rsrc_prec_compare(uvm_resource_base * rsrc1, uvm_resource_base * rsrc2);

    static uvm_resource_pool * m_pool;

    std::map<std::string, resource_q*> m_resource_q_map;
  
}; 

}  // namespace


#endif  // UVM_RESOURCE_POOL_H
