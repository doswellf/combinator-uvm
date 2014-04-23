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

#ifndef UVM_ML_CONFIG_RSRC_H
#define UVM_ML_CONFIG_RSRC_H

#include "bp_provided.h"
#include "base/uvm_component.h"
#include "base/uvm_resource_base.h"

using namespace std;
using namespace uvm;


//------------------------------------------------------------------------------
/*! @file uvm_ml_config_rsrc.h
 *  Adapter configuration and resource header implementing the required API.
 */

namespace uvm_ml {


//------------------------------------------------------------------------------
//! ML configuration handle for UVMSC configuration
//
class uvm_ml_config_handler : public uvm_component
{
public:
    UVM_COMPONENT_UTILS(uvm_ml_config_handler)

    uvm_ml_config_handler(sc_core::sc_module_name nm);
    uvm_ml_config_handler(sc_core::sc_module_name nm, bp_api_struct * bp_provided_api);
    ~uvm_ml_config_handler();

    void config_callback(std::string cntxt, std::string inst_name, std::string field_name, uvm_resource_base * rsrc);
    void rsrc_callback(uvm_rsrc_action action, std::string scope, std::string name, uvm_resource_base * rsrc);
    void process_frmw_notification(uvm_rsrc_action action, std::string scope, std::string name, uvm_resource_base * src, std::string cntxt = "");

private:
    static bp_api_struct * m_bp_provided_api;

};  // uvm_ml_config_handler

UVM_COMPONENT_REGISTER(uvm_ml_config_handler)

//------------------------------------------------------------------------------
//! ML config/rsrc interface for the SC adaptor.
//
class uvm_ml_config_rsrc 
{
public:

    static void Initialize(bp_api_struct *bp_provided_api);
    static void notify_config(const char *     cntxt,
                              const char *     instance_name,
                              const char *     field_name,
                              unsigned int     stream_size,
                              uvm_ml_stream_t  stream,
                              uvm_ml_time_unit time_unit,
                              double           time_value);

    static void process_bp_notification(uvm_ml_resource_notify_action action,
                                        const char *                  item_scope,
                                        const char *                  item_name,
                                        unsigned int                  stream_size,
                                        uvm_ml_stream_t               stream,
                                        uvm_ml_time_unit              time_unit,
                                        double                        time_value,
                                        const char *                  cntxt = "");

    static int notify_resource(uvm_ml_resource_notify_action action,
                               const char *                  item_scope,
                               const char *                  item_name,
                               const char *                  accessor_name,
                               unsigned int                  stream_size,
                               uvm_ml_stream_t               stream,
                               uvm_ml_time_unit              time_unit,
                               double                        time_value);
protected:
    template <typename T_val>
    static void call_db(uvm_ml_resource_notify_action action,
                        const char *                  cntxt,
                        const char *                  item_scope,
                        const char *                  item_name,
                        T_val                         val);

private:
    static uvm_ml_config_handler * m_config_handler;

}; // class uvm_ml_config_rsrc


template <typename T_val>
void uvm_ml_config_rsrc::call_db(uvm_ml_resource_notify_action action,
                                 const char *                  cntxt,
                                 const char *                  item_scope,
                                 const char *                  item_name,
                                 T_val                         val)
{
    switch(action)
    {
    case UVM_ML_RESOURCE_SET:
        uvm_resource_db<T_val>::set_default(item_scope, item_name);
        break;

    case UVM_ML_RESOURCE_SET_DEFAULT:
        uvm_resource_db<T_val>::set(item_scope, item_name, val);
        break;

    case UVM_ML_RESOURCE_SET_OVERRIDE:
    case UVM_ML_RESOURCE_SET_OVERRIDE_NAME:
        uvm_resource_db<T_val>::set_override(item_scope, item_name, val);
        break;

    case UVM_ML_RESOURCE_WRITE_BY_NAME:
        uvm_resource_db<T_val>::write_by_name(item_scope, item_name, val);
        break;
    
    case UVM_ML_CONFIG_SET:
        uvm_config_db<T_val>::set(cntxt, item_scope, item_name, val);
        break;

        default:
            break;
    };
}   // call_db()


}   // namespace


#endif  // UVM_ML_CONFIG_RSRC_H
