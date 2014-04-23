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

/*! @file uvm_resource_base.h
 *  Header file for UVM-SC resource_base
 */

#ifndef UVM_RESOURCE_BASE_H
#define UVM_RESOURCE_BASE_H

#include <string>
#include <systemc.h>
#include "base/uvm_object.h"
#include "base/uvm_factory.h"

namespace uvm {


enum uvm_resource_priority_e
{
    PRI_HIGH,
    PRI_LOW
};

const std::string uvm_regex_encap("/");


//----------------------------------------------------------------------
//! Base class for resources.
class uvm_resource_base : public sc_object
{
public:

    uvm_resource_base(const std::string& name, const std::string& scope = "*\\.");
    ~uvm_resource_base();

    void set_read_only();
    void set_read_write();
    bool is_read_only();
    void wait_modified();

    void set_scope(std::string scope);
    std::string get_scope();

    bool match_scope(std::string scope);

    void set_precedence(unsigned int precedence);
    unsigned int get_precedence();

    void set_priority(uvm_resource_priority_e priority);
    

    virtual std::string convert2string();
    virtual const std::type_info & get_value_type_id() = 0;

    static unsigned int m_default_precedence;

    // pure virtual functions for uvm_object
    void do_print(std::ostream& os) const {};
    void do_pack(uvm_packer& p) const {};
    void do_unpack(uvm_packer& p) {};
    void do_copy(const uvm_object* rhs) {};
    bool do_compare(const uvm_object* rhs) const {return true;};

    std::string get_name();


protected:
    bool              m_read_only;
    sc_core::sc_event m_modified_event;

private:

    std::string       m_scope;
    unsigned int      m_precedence;
    std::string       m_name;

};

}  // namespace

#endif // UVM_RESOURCE_BASE_H



