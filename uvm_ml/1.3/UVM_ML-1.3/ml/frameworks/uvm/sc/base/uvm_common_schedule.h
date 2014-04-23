//----------------------------------------------------------------------
//   Copyright 2012 Advanced Micro Devices Inc.
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

/*! \file uvm_common_schedule.h
  \brief Common schedule object.
*/
#ifndef UVM_COMMON_SCHEDULE_H
#define UVM_COMMON_SCHEDULE_H

#include "base/uvm_schedule.h"

namespace uvm {

//------------------------------------------------------------------------------
// Class: uvm_common_schedule
//  Schedule object
//------------------------------------------------------------------------------
/*! \class uvm_common_schedule
  \brief Schedule object.

  
*/
class uvm_common_schedule : public uvm_schedule
{
public:
    uvm_common_schedule(sc_module_name name);
    ~uvm_common_schedule();

    static uvm_common_schedule* get_uvm_common_schedule();
    static uvm_common_schedule* get_uvm_schedule();

    void virtual init();
    void virtual execute_build(uvm_component* pcomp);

    
private:
    static uvm_common_schedule*  _uvm_common_schedule;
    static uvm_common_schedule*  _uvm_schedule;
};

inline uvm_common_schedule* get_uvm_common_schedule() 
{
    return uvm_common_schedule::get_uvm_common_schedule();
}

inline uvm_common_schedule* get_uvm_schedule() 
{
    return uvm_common_schedule::get_uvm_schedule();
}

}  // namespace

#endif // UVM_SCHEDULE_COMMON_H



