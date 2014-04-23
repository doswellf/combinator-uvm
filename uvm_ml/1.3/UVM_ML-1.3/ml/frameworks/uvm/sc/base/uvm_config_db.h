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

#ifndef UVM_CONFIG_DB_H
#define UVM_CONFIG_DB_H


#include <algorithm>
#include "base/uvm_resource_db.h"
#include "base/uvm_common_schedule.h"
#include "base/uvm_phase.h"
#include "base/uvm_globals.h"

/*! @file uvm_config_db.h
 *  Header file for UVM-SC configuration DB
 */

namespace uvm {

class uvm_component;

typedef std::multimap<std::string, uvm_resource_base *> rsrc_map_type;
typedef std::map<std::string, rsrc_map_type*>           rsrc_cntxt_map_type;

static rsrc_cntxt_map_type m_rsrc_cntxt_map;

//----------------------------------------------------------------------
//! Configuration database - API for accessing/setting configurations.
/*! Derived class of uvm_resource_db<T>
 */
template<typename T>
class uvm_config_db :  public uvm_resource_db<T>
{
public:

    typedef uvm_resource<T> rsrc_t;

    uvm_config_db() : uvm_resource<T>() {}
    ~uvm_config_db() {}

    static bool get(uvm_component*    cntxt,
                    const std::string inst_name,
                    const std::string field_name,
                    T                 &value)
    {
        std::string cntxt_str;

        if (cntxt == NULL) 
            cntxt_str = "";
        else
            cntxt_str = uvm::uvm_get_cntxt_name(cntxt);
        
        return get(cntxt_str, inst_name, field_name, value);

    }

    static bool get(const std::string cntxt,
                    const std::string inst_name,
                    const std::string field_name,
                    T                 &value)
    {
        std::string         scope;
        uvm_resource_pool * rpool = uvm_resource_pool::get();
        resource_q          rsrc_q;
        rsrc_t            * rsrc;
        uvm_resource_base * rsrc_base = NULL;

        scope = cntxt;
        if (inst_name.compare("") != 0) 
            scope = scope + "." + inst_name;

        rsrc_q    = rpool->lookup_regex(scope, field_name, typeid(T));
        rsrc_base = rpool->get_highest_precedence(rsrc_q);
        rsrc = DCAST<rsrc_t*>(rsrc_base);

        if (rsrc == NULL)
        {
            return 0;
        }
        else
        {
            value = rsrc->read();
            return 1;
        }
    }

    static void set(uvm_component *   cntxt,
                    const std::string inst_name,
                    const std::string field_name,
                    const T &         value)
    {
        std::string cntxt_str;

        if (cntxt == NULL) 
            cntxt_str = "*";
        else
            cntxt_str = uvm::uvm_get_cntxt_name(cntxt);

        set(cntxt_str, inst_name, field_name, value);
    }


    static void set(const std::string cntxt,
                    const std::string inst_name,
                    const std::string field_name,
                    const T &         value)
    {
        std::string         scope;
        rsrc_map_type     * rsrc_map;
        rsrc_t            * rsrc = NULL;
        uvm_resource_base * rsrc_base;
        std::string         rsrc_key;
        uvm_phase         * curr_phase = uvm_common_schedule::get_uvm_common_schedule()->get_current_phase();
        std::pair <std::multimap<std::string, uvm_resource_base *>::iterator, std::multimap<std::string, uvm_resource_base *>::iterator> mit;

        if (cntxt.compare("") == 0) 
            scope = ".*";
        else 
            scope = cntxt;

        if (inst_name.compare("") != 0) 
            scope = cntxt +  "." + inst_name;

        if (m_rsrc_cntxt_map.find(cntxt) != m_rsrc_cntxt_map.end())
            rsrc_map = m_rsrc_cntxt_map[cntxt];
        else
            rsrc_map = new rsrc_map_type();

        rsrc_key = inst_name + "." + field_name;

        mit = rsrc_map->equal_range(rsrc_key);
        std::multimap<std::string, uvm_resource_base *>::iterator it = mit.first;
        while ((it != mit.second) && (rsrc == NULL))
        {
            rsrc_base = it->second;
            rsrc = DCAST<rsrc_t*>(rsrc_base);
            it++;
        }

        if (rsrc == NULL)
        {
            rsrc = new rsrc_t(field_name, scope);
            rsrc_map->insert(std::pair<std::string, uvm_resource_base*>(rsrc_key, rsrc));
        }

        if ( (curr_phase != NULL) && (curr_phase->get_name().compare("build") == 0))
            rsrc->set_precedence(uvm_resource_base::m_default_precedence - get_depth(cntxt));
        else
            rsrc->set_precedence(uvm_resource_base::m_default_precedence);

        rsrc->write(value);
        rsrc->set_override();

        uvm_config_callback(cntxt, inst_name, field_name, rsrc);
    }

    static bool exists(uvm_component * cntxt, std::string inst_name, std::string field_name)
    {
        std::string scope;

        if (cntxt == NULL) 
            scope = "";
        else
            scope = uvm::uvm_get_cntxt_name(cntxt);

        if (inst_name.compare("") != 0) 
            scope = scope + "." + inst_name;

        return uvm_resource_db<T>::exists(scope, field_name);
    }

    static void wait_modified(uvm_component * cntxt, std::string inst_name, std::string field_name)
    {
        rsrc_t      * rsrc;
        std::string   scope;

        if (cntxt == NULL) 
            scope = "";
        else
            scope = uvm::uvm_get_cntxt_name(cntxt);

        if (inst_name.compare("") != 0) 
            scope = scope + "." + inst_name;

        rsrc = uvm_resource_db<T>::get_by_name_regex(scope, field_name); 

        if (rsrc == NULL)
        {
            std::cout << "uvm_config_db::wait_modified() Resource not found (" 
                      << scope 
                      << "." 
                      << field_name
                      << ")\n";
        }
        else
        {
            rsrc->wait_modified();
        }

    }

    static unsigned int get_depth(std::string cntxt)
    {
        return std::count(cntxt.begin(), cntxt.end(), '.');    
    }


private:

};

template <typename T> 
void uvm_set_config_int(
  const std::string& instname,
  const std::string& field,
  const T& val
) {
  sc_dt::sc_bv<4096> bv = uvm_convert_to_bv(val);
  uvm_config_db<sc_dt::sc_bv<4096> >::set(0, instname, field, val);
}

}  // namespace

#endif // UVM_CONFIG_DB_H
