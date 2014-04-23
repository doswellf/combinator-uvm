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

/*! \file uvm_barrier.cpp
  \brief Implementation of the barrier syncronization object.
*/

#include "uvm_barrier.h"

namespace uvm {

//------------------------------------------------------------------------------
// Constructor: uvm_barrier
//------------------------------------------------------------------------------
uvm_barrier::uvm_barrier() :
    _n_barriers(0),
    _drain_time(SC_ZERO_TIME)
{
    
    uvm_callback_agent * p_callback_agent;

    p_callback_agent = new uvm_callback_agent();
    _callback_map[BARRIER_RAISE] = p_callback_agent;

    p_callback_agent = new uvm_callback_agent();
    _callback_map[BARRIER_DROP] = p_callback_agent;

    p_callback_agent = new uvm_callback_agent();
    _callback_map[BARRIER_ALL_DROP] = p_callback_agent;
}

//------------------------------------------------------------------------------
// Destructor: uvm_barrier
//------------------------------------------------------------------------------
uvm_barrier::~uvm_barrier()
{
    _callback_map.clear();
}

//------------------------------------------------------------------------------
// Function: wait
//  Wait until all barriers have been dropped.
//------------------------------------------------------------------------------
void uvm_barrier::wait(void)
{
    if ( _n_barriers )
        ::sc_core::wait(_barrier_event);
    else
        _barrier_event.notify(SC_ZERO_TIME);
}

//------------------------------------------------------------------------------
// Function: get_num_barrier
//   Returns the number of barrier that are still raised.
//
// Returns:
//  Number of barriers (int)
//------------------------------------------------------------------------------
int uvm_barrier::get_num_barriers(void)
{
    return _n_barriers;
}

//------------------------------------------------------------------------------
// Function: raise_barrier
//   Raise barrier
//
// Parameters:
//  count - number of barriers to raise (int)
//------------------------------------------------------------------------------
void uvm_barrier::raise_barrier(int count)
{
     _n_barriers += count;
     _raise_event.notify();

     uvm_callback_agent *p_callback_agent;
     p_callback_agent = _callback_map[BARRIER_RAISE];
     p_callback_agent->call();
}

//------------------------------------------------------------------------------
// Function: drop_barrier
//   Drop barrier
//
// Parameters:
//  count - number of barriers to drop (int)
//------------------------------------------------------------------------------
void uvm_barrier::drop_barrier(int count)
{
     if (_n_barriers >= count)
         _n_barriers -= count;
     else
        SC_REPORT_ERROR(100, "uvm_barrier::drop_barrier - barrier count drop below zero");
        //SC_REPORT_ERROR(UVM_ERROR_ID, "uvm_barrier::drop_barrier - barrier count drop below zero");
         
     uvm_callback_agent *p_callback_agent;
     p_callback_agent = _callback_map[BARRIER_DROP];
     p_callback_agent->call();

     if (_n_barriers == 0)
     {
        p_callback_agent = _callback_map[BARRIER_ALL_DROP];
        p_callback_agent->call();
     }

     _drop_event.notify();
     if (!_n_barriers)
         wait_drain_time();
}

//------------------------------------------------------------------------------
// Function: set_drain_time
//   Set the Drain time for the barrier
//
// Parameters:
//  drain_time - the amount of time to wait after all barriers have been dropped
//               before notifying event (sc_time)
//------------------------------------------------------------------------------
void uvm_barrier::set_drain_time (sc_core::sc_time drain_time)
{
    _drain_time = drain_time;
}

//------------------------------------------------------------------------------
// Function: get_drain_time
//   Returns the drain time
//
// Returns:
//  drain_time - the amount of time to wait after all barriers have been dropped
//               before notifying event (sc_time)
//------------------------------------------------------------------------------
sc_core::sc_time uvm_barrier::get_drain_time(void)
{
    return _drain_time;
}

//------------------------------------------------------------------------------
// Function: wait_drain_time
//   Wait a specified amount of time before triggering all barrier has been dropped
//------------------------------------------------------------------------------
void uvm_barrier::wait_drain_time()
{
    if (_drain_time != SC_ZERO_TIME)
        sc_core::wait(_drain_time, _raise_event);

     if (!_n_barriers)
         _barrier_event.notify(SC_ZERO_TIME);
}


//------------------------------------------------------------------------------
// Function : get_callback_agent()
//   - get a pointer to a particular callback agent
//------------------------------------------------------------------------------
uvm_callback_agent * uvm_barrier::get_callback_agent(uvm_barrier_cb_type barrier_action)
{
  return _callback_map[barrier_action];
}


} // namespace



