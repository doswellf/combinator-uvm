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


#define SC_INCLUDE_DYNAMIC_PROCESSES

#include "systemc.h"
#include "common/uvm_ml_config_rsrc.h"
#include "common/uvm_ml_adapter.h"
#include "common/uvm_ml_packer.h"
#include "uvm_ml_adapter_imp_spec_macros.h"
#include "base/uvm_globals.h"
#include "base/uvm_resource_t.h"
#include "base/uvm_config_db.h"


namespace uvm_ml {

enum uvm_ml_stream_kind_e
{
    UVM_ML_STREAM_NULL = 0,
    UVM_ML_STREAM_TYPED_OBJECT,
    UVM_ML_STREAM_RAW,
    UVM_ML_STREAM_STRING
};

bp_api_struct         * uvm_ml_config_handler::m_bp_provided_api = NULL;
uvm_ml_config_handler * uvm_ml_config_rsrc::m_config_handler     = NULL;
static bool             bp_set_config      = false;

//------------------------------------------------------------------------------
//! Configuration handler constrcutor
/*!
 */
uvm_ml_config_handler::uvm_ml_config_handler(sc_core::sc_module_name nm) :
    uvm_component(nm)
{
}

//------------------------------------------------------------------------------
//! Configuration handler constrcutor
/*!
 */
uvm_ml_config_handler::uvm_ml_config_handler(sc_core::sc_module_name nm, bp_api_struct * bp_provided_api) :
    uvm_component(nm)
{
    m_bp_provided_api = bp_provided_api;
    uvm_register_config_callback(this);
    uvm_register_rsrc_callback(this);
}

//------------------------------------------------------------------------------
//! Configuration handler destrcutor
/*!
 */
uvm_ml_config_handler::~uvm_ml_config_handler()
{
    uvm_unregister_config_callback(this);
}

//static int uvm_ml_in_export_notify_resource = 0; // VY
//------------------------------------------------------------------------------
//! Configuration handler Callback
/*! Called when a config_db.set() is executed
 *
 *  @param cntxt      - configuration context (hierarchy of component setting the rsrc)
 *  @param inst_name  - instance name the config applies to
 *  @param field_name - name of the resource
 *  @param rsrc       - base pointer to the resource
 */
void uvm_ml_config_handler::config_callback(std::string cntxt, std::string inst_name, std::string field_name, uvm_resource_base * rsrc)
{
    process_frmw_notification(UVM_CONFIG_SET, inst_name, field_name, rsrc, cntxt);
}   // config_callback

//------------------------------------------------------------------------------
//! Configuration handler Callback
/*! Called when a resource_db does any set action
 *
 *  @param action - resource action (eg. set, set_default ...)
 *  @param scope  - resource scope
 *  @param name   - name of the resource
 *  @param rsrc   - base pointer to the resource
 */
void uvm_ml_config_handler::rsrc_callback(uvm_rsrc_action action, std::string scope, std::string name, uvm_resource_base * rsrc)
{
    process_frmw_notification(action, scope, name, rsrc);
}   // rsrc_callback

void uvm_ml_config_handler::process_frmw_notification(uvm_rsrc_action action, std::string scope, std::string name, uvm_resource_base * rsrc, std::string cntxt)
{
    uvm_resource<string>              * rsrc_str;
    uvm_resource<uvm_object *>        * rsrc_obj;
    uvm_resource<sc_dt::sc_bv_base >  * rsrc_int;
    std::string                         str_val;
    uvm_object *                        obj_val;
    int                                 nbits;
    //sc_dt::sc_bv<4096>                  bv_val;

    if (bp_set_config)
    {
        bp_set_config = false;
        return;
    }

    //if (uvm_ml_in_export_notify_resource != 0) // VY: Do not send back the notification received from the backplane
    //return;
    uvm_ml_packed_obj & packed_obj = uvm_ml_utils::get_static_mlupo();
    sc_core::sc_time current_time  = sc_core::sc_time_stamp();
    double           time_sec      = current_time.to_seconds();
    unsigned         framework_id  = uvm_ml_utils::FrameworkId();
    uvm_ml_packer_int packer;

    if (rsrc->get_value_type_id() == typeid(std::string))
    {
        rsrc_str = DCAST<uvm_resource<string> *>(rsrc);
        if (rsrc_str == NULL)
        {
            cout << "ERROR: config_callback DCAST to string is NULL, should never happen!!" << endl;
        }
        else
        {
            str_val = rsrc_str->read();
            packer << UVM_ML_STREAM_STRING;
            packer << str_val;
            packer.fill_uvm_ml_packed_obj(&packed_obj);


            if (UVM_CONFIG_SET)
                (*m_bp_provided_api->notify_config_ptr)(framework_id, cntxt.c_str(), scope.c_str(), name.c_str(), packed_obj.size, packed_obj.val, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);
            else
                (*m_bp_provided_api->notify_resource_ptr)(framework_id, (uvm_ml_resource_notify_action) action, scope.c_str(), name.c_str(), scope.c_str(), packed_obj.size, packed_obj.val, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);

        }
    }
    else if (rsrc->get_value_type_id() == typeid(uvm_object*))
    {
        rsrc_obj = DCAST<uvm_resource<uvm_object *> *>(rsrc);
        if (rsrc_obj == NULL)
        {
            cout << "ERROR: config_callback DCAST to uvm_object * is NULL, should never happen!!" << endl;
        }
        else
        {
            obj_val = rsrc_obj->read();
            uvm_ml_packer_pack(obj_val, &packed_obj);

            if (UVM_CONFIG_SET)
                (*m_bp_provided_api->notify_config_ptr)(framework_id, cntxt.c_str(), scope.c_str(), name.c_str(), packed_obj.size, packed_obj.val, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);
            else
                (*m_bp_provided_api->notify_resource_ptr)(framework_id, (uvm_ml_resource_notify_action) action, scope.c_str(), name.c_str(), scope.c_str(), packed_obj.size, packed_obj.val, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);

        }
    }
    else if (rsrc->get_value_type_id() == typeid(sc_dt::sc_bv_base))
    {
        rsrc_int = DCAST<uvm_resource<sc_dt::sc_bv_base > *>(rsrc);
        if (rsrc_int == NULL)
        {
            cout << "ERROR: config_callback DCAST to sc_dt::sc_bv * is NULL, should never happen!!" << endl;
        }
        else
        {
            nbits = rsrc_int->get_nbits();

            sc_dt::sc_bv_base bv_val(nbits);
            bv_val = rsrc_int->read();
            packer << UVM_ML_STREAM_RAW;
            packer << bv_val;
            packer.fill_uvm_ml_packed_obj(&packed_obj);

            if (UVM_CONFIG_SET)
                (*m_bp_provided_api->notify_config_ptr)(framework_id, cntxt.c_str(), scope.c_str(), name.c_str(), packed_obj.size, packed_obj.val, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);
            else
                (*m_bp_provided_api->notify_resource_ptr)(framework_id, (uvm_ml_resource_notify_action) action, scope.c_str(), name.c_str(), scope.c_str(), packed_obj.size, packed_obj.val, (uvm_ml_time_unit) sc_core::SC_SEC, time_sec);
        }
    }

}   // process_frmw_notification

//------------------------------------------------------------------------------
//! Initialize ML Config/Resource handler
/*!
  * @param bp_provided_api - Pointer to Backplane provided API tray
 */
void uvm_ml_config_rsrc::Initialize(bp_api_struct *bp_provided_api)
{
    m_config_handler = new uvm_ml_config_handler("Config_Handler", bp_provided_api);

}   // Initialize()


//------------------------------------------------------------------------------
//! Notify Configuration Required API
/*!
 *  @param cntxt       - configuration context (hierarchy of component setting the rsrc)
 *  @param inst_name   - instance name the config applies to
 *  @param field_name  - name of the resource
 *  @param stream_size - size of data stream
 *  @param stream      - stream data
 *  @param time_unit   - current time unit
 *  @param time_value  - current time value
 */
void uvm_ml_config_rsrc::notify_config
(
    const char *     cntxt,
    const char *     instance_name,
    const char *     field_name,
    unsigned int     stream_size,
    uvm_ml_stream_t  stream,
    uvm_ml_time_unit time_unit,
    double           time_value
)
{
    process_bp_notification(UVM_ML_CONFIG_SET, instance_name, field_name, stream_size, stream, time_unit, time_value, cntxt); 

}   // notify_config

int uvm_ml_config_rsrc::notify_resource
(
    uvm_ml_resource_notify_action action,
    const char *                  item_scope,
    const char *                  item_name,
    const char *                  accessor_name,
    unsigned int                  stream_size,
    uvm_ml_stream_t               stream,
    uvm_ml_time_unit              time_unit,
    double                        time_value
)
{
    string cntxt = "";
    process_bp_notification(action, item_scope, item_name, stream_size, stream, time_unit, time_value); 
    return 1;

}   // notify_resource

void uvm_ml_config_rsrc::process_bp_notification
(
    uvm_ml_resource_notify_action action,
    const char *                  item_scope,
    const char *                  item_name,
    unsigned int                  stream_size,
    uvm_ml_stream_t               stream,
    uvm_ml_time_unit              time_unit,
    double                        time_value,
    const char *                  cntxt
)
{
    unsigned int         data_size = stream_size - UVM_ML_BLOCK_SIZE;
    std::string          str_val;
    uvm_object *         obj_val;
    sc_dt::sc_bv_base    bv_val((int) data_size);
    std::vector<unsigned> vec;
    uvm_ml_packer_int  packer;

    bp_set_config = true;
    uvm_ml_stream_t stream_data = stream;

    uvm_ml_packed_obj&  packed_obj = uvm_ml_utils::get_static_mlupo();


    // ENTER_CO_SIMULATION_CONTEXT();

    switch (stream[0])
    {
    case UVM_ML_STREAM_STRING:
        stream_data++;
        uvm_ml_utils::fill_mlupo(packed_obj, data_size, stream_data);
        packer.set_from_uvm_ml_packed_obj(&packed_obj);
        packer >> str_val;
        call_db(action, cntxt, item_scope, item_name, str_val);
        break;

    case UVM_ML_STREAM_TYPED_OBJECT:
        uvm_ml_utils::fill_mlupo(packed_obj, stream_size, stream);
        packer.set_from_uvm_ml_packed_obj(&packed_obj);
        packer >> obj_val;
        call_db(action, cntxt, item_scope, item_name, obj_val);
        break;

    case UVM_ML_STREAM_RAW:
        stream_data++;
        uvm_ml_utils::fill_mlupo(packed_obj, data_size, stream_data);
        packer.set_from_uvm_ml_packed_obj(&packed_obj);
        packer >> bv_val;
        call_db(action, cntxt, item_scope, item_name, bv_val);
        break;

    default:
        break;
    };

    //EXIT_CO_SIMULATION_CONTEXT();

}   // process_bp_notification()


}   // namespace



