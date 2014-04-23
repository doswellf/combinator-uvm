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

/*! \file uvm_barrier.h
  \brief Header file for UVM-SC barrier.
*/

#ifndef UVM_BARRIER_H
#define UVM_BARRIER_H

#include <systemc.h>
#include <map>
#include "base/uvm_callback.h"

namespace uvm {

enum uvm_barrier_cb_type
{
    BARRIER_RAISE,
    BARRIER_DROP,
    BARRIER_ALL_DROP    
};

//------------------------------------------------------------------------------
// Class: uvm_barrier
//  Synchronization object
//------------------------------------------------------------------------------
/*! \class uvm_barrier
  \brief Synchronization object.

  
*/
class uvm_barrier 
{
public:
    uvm_barrier();
    ~uvm_barrier();

    void wait(void);
    int get_num_barriers();
    void set_drain_time (sc_core::sc_time drain);
    sc_core::sc_time get_drain_time (void);
    void raise_barrier(int count = 1);
    void drop_barrier(int count = 1);

    uvm_callback_agent * get_callback_agent(uvm_barrier_cb_type barrier_action);


private:
    void wait_drain_time();

    int               _n_barriers;      // # of threads left to wait.
    sc_core::sc_time  _drain_time;
    sc_core::sc_event _barrier_event;   // Event to wait on.
    sc_core::sc_event _raise_event;
    sc_core::sc_event _drop_event;

    std::map<uvm_barrier_cb_type, uvm_callback_agent*> _callback_map;
};

}  // namespace

#endif // UVM_BARRIER_H
