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

/*! \file uvm_schedule.cpp
  \brief Implementation of the UVM-SC schedule.
*/
#define SC_INCLUDE_DYNAMIC_PROCESSES
#include "base/uvm_schedule.h"
#include "base/uvm_globals.h"
#include "base/uvm_component.h"
#include "uvm_imp_spec_macros.h"


namespace uvm {

using std::string;

//------------------------------------------------------------------------------
// Constructor: uvm_schedule
//------------------------------------------------------------------------------
uvm_schedule::uvm_schedule(sc_module_name name) :
    sc_module(name),
    _top_phase(NULL),
    _next_phase(NULL),
    _current_phase(NULL),
    _bcontinue(true),
    _bsim_start(false)
{
}

//------------------------------------------------------------------------------
// Destructor: uvm_schedule
//------------------------------------------------------------------------------
uvm_schedule::~uvm_schedule()
{
    std::map<std::string, uvm_phase*>::iterator it;

    for (it = _phase_map.begin(); it != _phase_map.end(); it++)
    {
        if (it->second != NULL)
            delete it->second;
    }
    _phase_map.clear();
}

//------------------------------------------------------------------------------
// Function: set_top_phase
//   Set the starting phase for this schedule
//
// Parameters:
//   name - name of top phase
//------------------------------------------------------------------------------
void uvm_schedule::set_top_phase(string name)
{
    _top_phase = _phase_map[name];
    _current_phase = _top_phase;

    if (_top_phase == NULL)
        cout << "ERROR: set_top_phase::unknown phase " << name << endl;
}

//------------------------------------------------------------------------------
// Function: set_top_phase
//   Set the starting phase for this schedule
//
// Parameters:
//   phase - pointer to phase
//------------------------------------------------------------------------------
bool uvm_schedule::set_top_phase(uvm_phase* phase)
{
    set_top_phase(phase->get_name());
}

//------------------------------------------------------------------------------
// Function: get_current_phase
//   Returns pointer to the current phase
//
// Returns:
//   phase - pointer to current phase
//------------------------------------------------------------------------------
uvm_phase* uvm_schedule::get_current_phase()
{
    return _current_phase;
}

//------------------------------------------------------------------------------
// Function: set_current_phase
//   Sets the current phase pointer
//
// Paramters:
//   phase - pointer to phase to set as current phase
//
// Returns:
//   phase - pointer to current phase
//------------------------------------------------------------------------------
uvm_phase* uvm_schedule::set_current_phase(uvm_phase *phase)
{
    _current_phase = phase;
    return _current_phase;
}


//------------------------------------------------------------------------------
// Function: set_current_phase
//   Sets the current phase pointer
//
// Paramters:
//   phase - name of phase to set as the current phase
//
// Returns:
//   phase - pointer to current phase
//------------------------------------------------------------------------------
uvm_phase* uvm_schedule::set_current_phase(string phase)
{
    _current_phase = _phase_map[phase];
    return _current_phase;
}


//------------------------------------------------------------------------------
// Function: add_phase
//   Add a phase to the schedule and returns the phase pointer.
//
// Parameters:
//  name - name of phase to add
//
// Returns:
//   phase - pointer to phase
//------------------------------------------------------------------------------
uvm_phase* uvm_schedule::add_phase(string name, uvm_phase_type type, uvm_phase_order order)
{
    uvm_phase* phase;

    phase = new uvm_phase(name, this, type, order);
    _phase_map[name] = phase;

    return phase;
}

//------------------------------------------------------------------------------
// Function: add_phase
//   Add a phase to the schedule.
//
// Parameters:
//  phase - phase to be added
//
//------------------------------------------------------------------------------
void uvm_schedule::add_phase(uvm_phase* pphase)
{
    _phase_map[pphase->get_name()] = pphase;
}

//------------------------------------------------------------------------------
// Function: add_arc
//   Add an arc
//
// Parameters:
//  from_phase - name of phase arc starts from
//  to_phase   - name of phase arc goes to
//------------------------------------------------------------------------------
void uvm_schedule::add_arc(string from_phase, string to_phase, unsigned int priority)
{
    uvm_phase* pfrom_phase = _phase_map[from_phase];
    uvm_phase* pto_phase   = _phase_map[to_phase];
    
    if (pfrom_phase == NULL)
        cout << "ERROR : add_arc:: phase does not exist " << from_phase << endl;
    else if (pto_phase == NULL)
        cout << "ERROR : add_arc:: phase does not exist " << to_phase << endl;
    else
        pfrom_phase->add_next_phase(pto_phase, priority);


}

//------------------------------------------------------------------------------
// Function: add_arc
//   Add an arc
//
// Parameters:
//  from_phase - pointer of phase arc starts from
//  to_phase   - pointer of phase arc goes to
//
// Returns:
//  status - return false if either phase pointer does not exists in the pool
//------------------------------------------------------------------------------
void uvm_schedule::add_arc(uvm_phase* pfrom_phase, uvm_phase* pto_phase, unsigned int priority)
{
    add_arc(pfrom_phase->get_name(), pto_phase->get_name(), priority);
}

//------------------------------------------------------------------------------
// Function: go_to_phase
//   Specify the next phase to go to.
//
// Parameters:
//  name - name of the phase to go to
//
//------------------------------------------------------------------------------
void uvm_schedule::go_to_phase(string name)
{
    uvm_phase* pphase = _phase_map[name];
    if (pphase == NULL)
    {
        cout << "ERROR : go_to_phase:: phase does not exist " << name << endl;
    }
    else
    {
        _current_phase->go_to_phase(pphase);
    }

}

//------------------------------------------------------------------------------
// Function: go_to_phase
//   Specify the next phase to go to.
//
// Parameters:
//  phase - pointer to phase to go to.
//------------------------------------------------------------------------------
void uvm_schedule::go_to_phase(uvm_phase* phase)
{
    go_to_phase(phase->get_name());
}


//------------------------------------------------------------------------------
// Function: get_phase
//   Returns a pointer to the name phase
//
// Parameters:
//  name - name of the phase to get
//
// Returns:
//  phase - pointer to named phase
//------------------------------------------------------------------------------
uvm_phase* uvm_schedule::get_phase(string name)
{
    return _phase_map[name];
}


void uvm_schedule::start_schedule(uvm_component* pcomp)
{
    if (_current_phase == NULL) return;

    sc_process_handle proccess_h;

    while ((_current_phase != NULL) &&
            (_bcontinue))
    {
        execute_schedule(pcomp);
        if (_current_phase->get_phase_state() == UVM_PHASE_DONE)
            _current_phase = _next_phase;
    }
}

//------------------------------------------------------------------------------
// Function: execute
//   Main execution for schedule
//------------------------------------------------------------------------------
void uvm_schedule::execute_schedule(uvm_component *pcomp)
{
    uvm_phase* next_phase;
    bool bready;

    if (_current_phase == NULL)
    {
        cout << "WARNING: uvm_schedule::execute_schedule() current phase is NULL" << endl;
        return;
    }

    if (_current_phase->get_phase_type() == UVM_RUNTIME_PHASE)
        execute_runtime_phase(pcomp);
    else
        execute_nonruntime_phase(pcomp);
}

//------------------------------------------------------------------------------
// Function: execute_nonruntime_phase
//   Main execution for non-runtime phases
//------------------------------------------------------------------------------
void uvm_schedule::execute_nonruntime_phase(uvm_component *pcomp)
{
    uvm_phase* next_phase;
    bool bready;
    sc_process_handle barrier_h;
    uvm_phase_state phase_state = _current_phase->get_phase_state();

    switch(phase_state)
    {
    case UVM_PHASE_DORMANT:
        _current_phase->set_phase_state(UVM_PHASE_READY_TO_START);

        break;

    case UVM_PHASE_READY_TO_START:
        bready = _current_phase->is_sync_point_ready(UVM_SYNC_AT_START);

        if (!bready)
            _current_phase->wait_ready_to_start();

        _current_phase->set_phase_state(UVM_PHASE_EXECUTING);

    case UVM_PHASE_EXECUTING:

        _current_phase->execute(pcomp);
        //_current_phase->set_phase_state(UVM_PHASE_ENDED);
        _current_phase->set_phase_state(UVM_PHASE_DONE);
        _next_phase = _current_phase->get_next_phase();
        _current_phase->clear_next_phase_req();      // clear out next phase request list

        break;
    case UVM_PHASE_ENDED:
        _next_phase = _current_phase->get_next_phase();
        _current_phase->clear_next_phase_req();      // clear out next phase request list
        _current_phase->set_phase_state(UVM_PHASE_DONE);

        break;
    default:
        cout << "ERROR: invalid state" << endl;
        break;
    };
}

//------------------------------------------------------------------------------
// Function: execute_runtime_phase
//   Main execution for runtime phases
//------------------------------------------------------------------------------
void uvm_schedule::execute_runtime_phase(uvm_component *pcomp)
{
    uvm_phase* next_phase;
    bool bready;
    sc_process_handle barrier_h;
    uvm_phase_state phase_state = _current_phase->get_phase_state();
    sc_time dur(5, SC_NS);

    switch(phase_state)
    {
    case UVM_PHASE_DORMANT:
        _current_phase->set_phase_state(UVM_PHASE_READY_TO_START);

        break;

    case UVM_PHASE_READY_TO_START:
        if (!_bsim_start)
        {
            wait(_sim_start_ev);
            }

        bready = _current_phase->is_sync_point_ready(UVM_SYNC_AT_START);

        if (!bready)
            _current_phase->wait_ready_to_start();

        _current_phase->execute(pcomp);
        _current_phase->set_phase_state(UVM_PHASE_EXECUTING);
        break;
    case UVM_PHASE_EXECUTING:

        _current_phase->execute(pcomp);
        barrier_h = sc_spawn(sc_bind(&uvm_schedule::wait_barrier, this));
        wait(barrier_h.terminated_event());

        bready = _current_phase->is_sync_point_ready(UVM_SYNC_AT_END);
        if (!bready)
            _current_phase->wait_ready_to_end();

        _current_phase->set_phase_state(UVM_PHASE_READY_TO_END);
        break;
    case UVM_PHASE_READY_TO_END:
        _current_phase->execute(pcomp);
        _current_phase->set_phase_state(UVM_PHASE_ENDED);
        break;
    case UVM_PHASE_ENDED:
        _current_phase->execute(pcomp);
        _next_phase = _current_phase->get_next_phase();
        _current_phase->clear_next_phase_req();      // clear out next phase request list
        _current_phase->set_phase_state(UVM_PHASE_DONE);

        break;
    default:
        break;
    };
}

//------------------------------------------------------------------------------
// Function: init
//   Initialize the schedule
//------------------------------------------------------------------------------
void uvm_schedule::init(void)
{
    if (_top_phase == NULL)
    {
        cout << "uvm_schedule::init - top phase not set for schedule - " << name() << endl;
        exit(1);
    }

    _current_phase = _top_phase;
    _current_phase->set_phase_state(UVM_PHASE_READY_TO_START);

    //TODO
    //uvm_component* pcomp = uvm_get_top();
    uvm_component* pcomp = NULL;
    // TODO: a non uvm_component top or no top, don't execute
    if (pcomp == NULL)
    {
        cout << "uvm_schedule::init - no top component detected, exiting" << endl;
    }
    else
    {
        sc_spawn(sc_bind(&uvm_schedule::start_schedule, this, pcomp));
    }
}


//------------------------------------------------------------------------------
// Function: wait_barrier
//   Wait for barrier to be cleared
//------------------------------------------------------------------------------
void uvm_schedule::wait_barrier(void)
{
    _current_phase->barrier.wait();
}

//------------------------------------------------------------------------------
// Function: set_max_runtime
//   Set the max_runtime for a phase state
//------------------------------------------------------------------------------
void uvm_schedule::set_max_runtime(sc_core::sc_time max_runtime)
{
    _max_runtime = max_runtime;
}

//------------------------------------------------------------------------------
// Function: set_continue
//   Set to true if the schedule should automatically continue to next state
//------------------------------------------------------------------------------
void uvm_schedule::set_continue(bool bcontinue)
{
    _bcontinue = bcontinue;
}

//------------------------------------------------------------------------------
// Function: start_of_simulation
//   Start of simulation call back from SystemC
//------------------------------------------------------------------------------
void uvm_schedule::start_of_simulation()
{
    _bsim_start = true;
    _sim_start_ev.notify();
}

//------------------------------------------------------------------------------
// Function: register_callback
//   Register component to all phases in schedule
//
// Parameter:
//   pcomp - ptr to component
//------------------------------------------------------------------------------
void uvm_schedule::register_callback(uvm_component* pcomp)
{
    std::map<string, uvm_phase*>::iterator it;

    for (it = _phase_map.begin(); it != _phase_map.end(); it++)
    {
        it->second->register_comp_callback(pcomp);
    }
}

//------------------------------------------------------------------------------
// Function: execute_phase
//   
//
// Parameter:
//------------------------------------------------------------------------------
int uvm_schedule::execute_phase(string phase_name, uvm_phase_state state, sc_core::sc_module* pmod)
{
    uvm_phase *pphase = _phase_map[phase_name]; 
    char msg[1024];

    if (pphase == NULL)
    {
        if (phase_name.compare("resolve_bindings") == 0)
        {
            return 1;
        }
        else
        {
            sprintf(msg, "phase = %s", phase_name.c_str());
            return 0;
        }
    }

    _current_phase = pphase;
    _current_phase->set_phase_state(state);
    _current_phase->execute(pmod);

    return 1;
}

//------------------------------------------------------------------------------
// Function: execute_quasi_static_phase
//   
//
// Parameter:
//------------------------------------------------------------------------------
int uvm_schedule::execute_quasi_static_phase(string phase_name, uvm_phase_state state)
{
    char msg[1024];
    uvm_phase *pphase = _phase_map[phase_name]; 
    static bool bresolve_bindings = false;


    if ( (phase_name.compare("resolve_bindings") == 0) &&
         (state == UVM_PHASE_EXECUTING)  &&
         (bresolve_bindings == false) )
    {
        bresolve_bindings = true;
        QUASI_STATIC_COMPLETE_BINDING();
        return 1;
    }

    if (pphase == NULL)
    {
        sprintf(msg, "phase = %s", phase_name.c_str());
        return 1; // It's legitimate to receive notification about the unknown phase
    }

    _current_phase = pphase;
    _current_phase->set_phase_state(state);

    if (state == uvm::UVM_PHASE_READY_TO_START)
        return _current_phase->start();
    else if (state == uvm::UVM_PHASE_ENDED)
        return _current_phase->end();
    else    
        return 1;
}

} // namespace




