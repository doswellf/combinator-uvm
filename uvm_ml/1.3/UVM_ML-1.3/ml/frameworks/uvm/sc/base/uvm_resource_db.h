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
#ifndef UVM_RESOURCE_DB_H
#define UVM_RESOURCE_DB_H

/*! @file uvm_resource_db.h
 *  Header file for UVM-SC resource DB
 */


#include <string>
#include <typeinfo>
#include "base/uvm_resource_pool.h"
#include "base/uvm_resource_t.h"
#include "base/uvm_globals.h"

namespace uvm {


//----------------------------------------------------------------------
//! Resource database - API for accessing/setting resources.
//
template<class T>
class uvm_resource_db
{
public:
    typedef uvm_resource<T>* rsrc_ptr_t;
    typedef uvm_resource<T>  rsrc_t;

    //----------------------------------------------------------------------
    //! Constructor
    //
    uvm_resource_db() {};


    //----------------------------------------------------------------------
    //! Desstructor
    //
    ~uvm_resource_db() {};
    
    //----------------------------------------------------------------------
    //! Find the highest precedence resource of this type.
    /*!
     *  @param scope - Resource scope
     *  @param name  - Name of resource
     *
     *  @return Pointer to resource
     */
    static rsrc_ptr_t get_by_name(std::string scope, std::string name)
    {
        uvm_resource_base * rsrc_base = NULL;
        rsrc_ptr_t rsrc = NULL;

        uvm_resource_pool * rpool = uvm_resource_pool::get();
        //rsrc = rpool->get_by_name(scope, name, typeid(rsrc_ptr_t));
        rsrc_base = rpool->get_by_name(scope, name, typeid(rsrc_ptr_t));
        if (rsrc_base != NULL)
            rsrc = DCAST<rsrc_ptr_t> (rsrc_base);
        return rsrc;
    }

    //----------------------------------------------------------------------
    //! Find the highest precedence resource of this type, where name could be
    /*! regular expression.
     *
     *  @param scope - Resource scope
     *  @param name  - Name of resource (regex)
     *
     *  @return Pointer to resource
     */
    static rsrc_ptr_t get_by_name_regex(std::string scope, std::string name)
    {
        rsrc_ptr_t rsrc = NULL;

        uvm_resource_pool * rpool = uvm_resource_pool::get();
        rsrc = rpool->get_by_name_regex(scope, name, typeid(rsrc_ptr_t));
    }


    //----------------------------------------------------------------------
    //! Create a resource of this type with specified name, scope and 
    /*! default value.  Add to the resource to the back of the resource pool.
     *
     *  @param scope - Resource scope
     *  @param name  - Name of resource
     *
     *  @return Pointer to resource created.
     */
    static rsrc_ptr_t set_default(std::string scope, std::string name)
    {
        rsrc_ptr_t rsrc = new rsrc_t(name, scope);
        rsrc->set();
        uvm_rsrc_callback(UVM_RESOURCE_SET_DEFAULT, scope, name, rsrc);
    }

    //----------------------------------------------------------------------
    //! Create a resource of this type with specified name, scope and value.
    /*! Add to the resource to the back of the resource pool.
     *
     *  @param scope - Resource scope
     *  @param name  - Name of resource
     *  @param value - Value to set for the object contained in the resource
     */
    static void set(std::string scope, std::string name, T value)
    {
        rsrc_ptr_t rsrc = new rsrc_t(name, scope);
        rsrc->write(value);
        rsrc->set();
        uvm_rsrc_callback(UVM_RESOURCE_SET, scope, name, rsrc);
    }

    //----------------------------------------------------------------------
    //! Create a resource of this type with specified name, scope and value.
    /*! Add to the resource to the front of the resource pool.
     *
     *  @param name  - Name of resource
     *  @param scope - Resource scope
     *  @param value - Value to set for the object contained in the resource
     */
    static void set_override(std::string scope, std::string name, T value)
    {
        rsrc_ptr_t rsrc = new rsrc_t(name, scope);
        rsrc->write(value);
        rsrc->set_override();
        uvm_rsrc_callback(UVM_RESOURCE_SET_OVERRIDE, scope, name, rsrc);
    }

    //----------------------------------------------------------------------
    //! Return the value of the resource specified by name and scope.
    /*! 
     *  @param scope - Resource scope
     *  @param name  - Name of resource
     *  @param value - Reference to value of object contained in resource
     *
     *  @return Status of read.
     *          - 0 Read unsuccessful, resource not found
     *          - 1 Successful read
     */
    static bool read_by_name(std::string scope, std::string name, T &value)
    {
        bool       bsuccess = false;
        rsrc_ptr_t rsrc     = get_by_name(scope, name);

        if (rsrc != NULL)
        {
            value = rsrc->read();
            bsuccess = true;
        }
        return bsuccess;

    }

    //----------------------------------------------------------------------
    //! Write 'value' into the resource specified by name and scope.
    /*! 
     *  @param scope - Resource scope
     *  @param name  - Name of resource
     *  @param value - Value to write to the object contained in resource
     *
     *  @return Status of write.
     *          - 0 Write unsuccessful, resource not found
     *          - 1 Successful write
     */
    static bool write_by_name(std::string scope, std::string name, T value) 
    {
        bool       bsuccess = false;
        rsrc_ptr_t rsrc     = get_by_name(scope, name);

        if (rsrc != NULL)
        {
            rsrc->write(value);
            bsuccess = true;
        }

        uvm_rsrc_callback(UVM_RESOURCE_WRITE_BY_NAME, scope, name, rsrc);
        return bsuccess;
    }

    //----------------------------------------------------------------------
    //! Check to see if the resource exist in the specified scope
    /*! 
     *  @param scope - Resource scope
     *  @param name  - Name of resource
     *
     *  @return Status 
     *          - 0 Resource doesn't exist
     *          - 1 Resource exist  
     */
    static bool exists(std::string scope, std::string name)
    {
        if (get_by_name(scope, name) != NULL)
            return 1;
        else
            return 0;
    }

};

}   // namespace

#endif // UVM_RESOURCE_DB_H

