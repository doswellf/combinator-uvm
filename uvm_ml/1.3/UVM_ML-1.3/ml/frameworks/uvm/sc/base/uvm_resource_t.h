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

/*! @file uvm_resource_t.h
 *  Header file for UVM-SC parametrized resource class
 */

#ifndef UVM_RESOURCE_T_H
#define UVM_RESOURCE_T_H

namespace uvm {


//----------------------------------------------------------------------
//! Parametrized class for resources.
//
template<typename T>
class uvm_resource :  public uvm_resource_base
{
public:

    
    //----------------------------------------------------------------------
    //! Constructor
    /*!
     *  @param name  - Name of resource
     *  @param scope - Resource scope
     *
     */
    uvm_resource(const std::string& name, const std::string& scope = "*\\.") :
        uvm_resource_base(name, scope)
    {
    }

    //----------------------------------------------------------------------
    //! Desstructor
    //
    ~uvm_resource() {};


    //----------------------------------------------------------------------
    //! Add the resource to the back of the pool.
    //
    void set() 
    {
        uvm_resource_pool * rpool = uvm_resource_pool::get();
        rpool->set(this);
    }

    //----------------------------------------------------------------------
    //! Add the resource to front the pool.
    //
    void set_override()
    {
        uvm_resource_pool * rpool = uvm_resource_pool::get();
        rpool->set_override(this);
    }

    //----------------------------------------------------------------------
    //! Return the object value.
    //
    T read()
    {
        return m_value;
    }

    //----------------------------------------------------------------------
    //! Modified the stored value of the object.
    /*
     *  @param value - New value of object. 
     */
    void write(T value)
    {
        if (m_read_only)
        {
            std::cout << "ERROR: uvm_resource_t::write() Resource is read-only" << std::endl;
        }
        else if (value != m_value)
        {
            m_value = value;
            m_modified_event.notify();
        }
    }

    //----------------------------------------------------------------------
    //! Get the type id of the value field
    /*
     *  @return typeid - Typeid of value field
     */
    const std::type_info & get_value_type_id()
    {
        return typeid(m_value);    
    }



protected:

    T m_value;

};


//----------------------------------------------------------------------
//! Specialization class for sc_bv_base
//
template<>
class uvm_resource<sc_bv_base> :  public uvm_resource_base
{
public:

    
    //----------------------------------------------------------------------
    //! Constructor
    /*!
     *  @param name  - Name of resource
     *  @param scope - Resource scope
     *
     */
    uvm_resource(const std::string& name, const std::string& scope = "*\\.") :
        uvm_resource_base(name, scope),
        m_value(NULL)
    {
    }

    //----------------------------------------------------------------------
    //! Desstructor
    //
    ~uvm_resource() 
    {
        if (m_value) delete m_value;
    }


    //----------------------------------------------------------------------
    //! Add the resource to the back of the pool.
    //
    void set() 
    {
        uvm_resource_pool * rpool = uvm_resource_pool::get();
        rpool->set(this);
    }

    //----------------------------------------------------------------------
    //! Add the resource to front the pool.
    //
    void set_override()
    {
        uvm_resource_pool * rpool = uvm_resource_pool::get();
        rpool->set_override(this);
    }

    //----------------------------------------------------------------------
    //! Return the object value.
    //
    sc_bv_base read()
    {
        sc_bv_base bv(m_value->length());
        bv = *m_value;
        return bv;
    }

    //----------------------------------------------------------------------
    //! Modified the stored value of the object.
    /*
     *  @param value - New value of object. 
     */
    void write(sc_bv_base value)
    {
        if (m_read_only)
        {
            std::cout << "ERROR: uvm_resource_t::write() Resource is read-only" << std::endl;
        }
        else
        {
            if ( (m_value != NULL) &&
                 (m_value->length() != value.length()) )
            {
                delete m_value;
            }

            if (m_value == NULL)
            {
                m_value = new sc_bv_base(value.length());
            }

            if (value != *m_value)
            {
                *m_value = value;
                m_modified_event.notify();
            }
        }
    }

    //----------------------------------------------------------------------
    //! Get the type id of the value field
    /*
     *  @return typeid - Typeid of value field
     */
    const std::type_info & get_value_type_id()
    {
        return typeid(sc_bv_base);    
    }

    //----------------------------------------------------------------------
    //! Return number of bits of the resource value
    /*
     *  @return Number of bits of the resource value
     */
    int get_nbits()
    {
        return m_value->length();
    }



protected:

    sc_bv_base * m_value;

};  // uvm_resource_t<sc_bv_base>

}   // namespace

#endif  // UVM_RESOURCE_T_H
