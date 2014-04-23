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

/*! \file uvm_common_phase.cpp
  \brief Implementation of UVM-ML phasing.
*/
#define SC_INCLUDE_DYNAMIC_PROCESSES
#include "base/uvm_common_phase.h"
#include "base/uvm_component.h"
#include "base/uvm_schedule.h"
#include "base/uvm_globals.h"
#include "uvm_imp_spec_macros.h"

namespace uvm {

using std::string;

//------------------------------------------------------------------------------
// Constructor: uvm_common_phase
//------------------------------------------------------------------------------
uvm_common_phase::uvm_common_phase(string name, uvm_schedule *p_schedule, uvm_phase_type type, uvm_phase_order phase_order) :
    uvm_phase(name, p_schedule, type, phase_order)
{

}

//------------------------------------------------------------------------------
// Destructor: uvm_common_phase
//------------------------------------------------------------------------------
uvm_common_phase::~uvm_common_phase()
{
}


/*
//------------------------------------------------------------------------------
// Function: execute
//  Execute callback
//
// Parameters:
//  state - what callback to call (start_phase, ready_to_end)
//------------------------------------------------------------------------------
void uvm_common_phase::execute(uvm_component* pcomp)
{
    uvm_component *pchild;
    uvm_component *pcomp_callback;
    int num_children;
    std::vector<uvm_component*> child_vec;
    uvm_callback_agent *p_callback_agent;
    uvm_component* comp;
    sc_module * pmodule;

    if (_type == RUNTIME_PHASE)
    {
        for (unsigned int i = 0; i < _comp_callback_vec.size(); i++)
        {
            pcomp_callback = _comp_callback_vec[i];

            switch(_state)
            {
            case PHASE_READY_TO_START:
                pcomp_callback->phase_started(this); 
                break;
            case PHASE_EXECUTING:
            std::cout << "spawning off run phase" << std::endl;
                if (_name.compare("run") == 0) 
                {
                    sc_spawn(sc_bind(&uvm_component::run_phase, pcomp_callback, this));
                    }
                else if (_name.compare("reset") == 0) 
                    pcomp_callback->reset_phase(this); 
                else if (_name.compare("configure") == 0) 
                    pcomp_callback->configure_phase(this); 
                else if (_name.compare("main") == 0) 
                    pcomp_callback->main_phase(this); 
                else if (_name.compare("shutdown") == 0) 
                    pcomp_callback->shutdown_phase(this); 
                else
                    pcomp_callback->phase_execute(this); 
                break;
            case PHASE_READY_TO_END:
                pcomp_callback->phase_ready_to_end(this); 
                break;
            case PHASE_ENDED:
                pcomp_callback->phase_ended(this); 
                break;
            default:
                break;
            }
        }

        p_callback_agent = _callback_map[_state];
        p_callback_agent->call();

    }
    else
    {

        if (_state != PHASE_EXECUTING)
            cout << "ERROR: Non-runtime phases, can only be executed" << endl;

        comp = pcomp;
        // TODO
        //if (comp == NULL)
        //    comp = uvm_get_top();
        //
        
        if (comp != NULL)
        {
            switch (_order)
            {
            case TOP_DOWN:

                if (_name.compare("build") == 0)
                {
                    pmodule = comp;
                    sc_get_curr_simcontext()->hierarchy_push(pmodule);
                    comp->build_phase(this);
                }
                else if (_name.compare("final") == 0)
                    comp->final_phase(this);
                else
                    comp->phase_execute(this);


                // Find child 
                child_vec = uvm_get_children(mod_vec[i]);
                for (j = 0; j < child_vec.size(); j++)
                {
                    execute(child_vec[j]);
                }
                if (_name.compare("build") == 0)
                    sc_get_curr_simcontext()->hierarchy_pop();
                break;
            case BOTTOM_UP:
                child_vec = uvm_get_children(mod_vec[i]);
                for (k = 0; k < child_vec.size(); k++)
                {
                    execute(child_vec[k]);
                }
                comp = DCAST<uvm_component*>(mod_vec[i]);


                if (_name.compare("extract") == 0)
                    comp->extract_phase(this);
                else if (_name.compare("check") == 0)
                    comp->check_phase(this);
                else if (_name.compare("report") == 0)
                    comp->report_phase(this);
                else
                    comp->phase_execute(this);
                break;
            default:
                break;
            };

            p_callback_agent = _callback_map[PHASE_EXECUTING];
            p_callback_agent->call();
        }
        else
        {
            cout << "uvm_common_phase::execute() - no component top detected" << endl;
        }

    }
}
*/


//------------------------------------------------------------------------------
// Function: process_state_executing_runtime
//
// Parameters:
//------------------------------------------------------------------------------
void uvm_common_phase::process_state_executing_runtime(uvm_component *pcomp)
{
    sc_process_handle process_handle;

    if (_name.compare("run") == 0) 
    {
        process_handle = sc_spawn(sc_bind(&uvm_component::run_phase, pcomp, this));
        pcomp->set_run_handle(process_handle);
    }
    else if (_name.compare("reset") == 0) 
    {
        process_handle = sc_spawn(sc_bind(&uvm_component::reset_phase, pcomp, this));
        pcomp->set_reset_handle(process_handle);
    }
    else if (_name.compare("configure") == 0) 
    {
        process_handle = sc_spawn(sc_bind(&uvm_component::configure_phase, pcomp, this));
        pcomp->set_configure_handle(process_handle);
    }
    else if (_name.compare("main") == 0) 
    {
        process_handle = sc_spawn(sc_bind(&uvm_component::main_phase, pcomp, this));
        pcomp->set_main_handle(process_handle);
    }
    else if (_name.compare("shutdown") == 0) 
    {
        process_handle = sc_spawn(sc_bind(&uvm_component::shutdown_phase, pcomp, this));
        pcomp->set_shutdown_handle(process_handle);
    }
    else
    {
        pcomp->phase_execute(this); 
    }
}

//------------------------------------------------------------------------------
// Function: process_state_executing_nonruntime
//
// Parameters:
//------------------------------------------------------------------------------
void uvm_common_phase::process_state_executing_nonruntime(sc_core::sc_module *pmod)
{
    if (get_phase_type() != UVM_POSTRUN_PHASE) { // postrun phases are not generalized yet
        int result = do_execute(pmod);
        if (result && (CHECK_STOP_AT_PHASE_END() == true))
	    result = 0;
    }
    else {
        uvm_component* pcomp = DCAST<uvm_component*>(pmod); 
        if (pcomp != NULL) {
            if (_name.compare("final") == 0)
                pcomp->final_phase(this);
            else if (_name.compare("extract") == 0)
                pcomp->extract_phase(this);
            else if (_name.compare("check") == 0)
                pcomp->check_phase(this);
            else if (_name.compare("report") == 0)
                pcomp->report_phase(this);
            else
                pcomp->phase_execute(this);
        }
    }
}

//------------------------------------------------------------------------------
// Phase specific functionality
//------------------------------------------------------------------------------

int uvm_build_phase::do_execute(sc_core::sc_module * pmod)
{
    int result = 1;
    try
    {
        NODE_CONSTRUCTION_DONE(pmod) // Calls construction_done() callback
                                     // For non-uvm_component sc_module - 
                                     // that directly calls before_end_of_elaboration()
                                     // For uvm_component it calls build() which, 
                                     // if not overriden, invokes before_end_of_elaboration()
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_build_phase::end()
{
    int result = 1;
    try
    {
        QUASI_STATIC_END_OF_CONSTRUCTION()
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_connect_phase::do_execute(sc_core::sc_module * pmod)
{
    int result = 1;
    try
    {
        NODE_CONNECT(pmod)
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_end_of_elaboration_phase::do_execute(sc_core::sc_module * pmod)
{
    int result = 1;
    try
    {
        NODE_END_OF_ELABORATION(pmod)
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_end_of_elaboration_phase::end()
{
    int result = 1;
    try
    {
#ifndef SIMCONTEXT_EXTENSIONS_OUT
        QUASI_STATIC_END_OF_ELABORATION()
#endif
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_start_of_simulation_phase::do_execute(sc_core::sc_module * pmod)
{
    int result = 1;
    try
    {
        NODE_START_OF_SIMULATION(pmod)
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_start_of_simulation_phase::end()
{
    int result = 1;
    try
    {
#ifndef SIMCONTEXT_EXTENSIONS_OUT
        QUASI_STATIC_START_OF_SIMULATION()
#endif
        QUASI_STATIC_PREPARE_TO_SIMULATE()
    }
    catch (int)
    {
        result = 0;
    }
    return result;
}

int uvm_run_phase::start()
{
    return 1;
}

} // namespace




