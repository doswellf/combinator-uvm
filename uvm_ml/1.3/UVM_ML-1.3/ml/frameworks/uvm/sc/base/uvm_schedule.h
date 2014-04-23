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

/*! \file uvm_schedule.h
  \brief Header file for the UVM-SC schedule.
*/
#ifndef UVM_SCHEDULE_H
#define UVM_SCHEDULE_H

#include <string>
#include "base/uvm_phase.h"

namespace uvm {

//------------------------------------------------------------------------------
// Class: uvm_schedule
//  Schedule object
//------------------------------------------------------------------------------
/*! \class uvm_schedule
  \brief Schedule object.

  
*/
class uvm_schedule : public sc_module
{
public:

    uvm_schedule(sc_module_name name);
    ~uvm_schedule();

    void set_top_phase(std::string name);
    bool set_top_phase(uvm_phase* phase);

    uvm_phase* get_current_phase();
    uvm_phase* set_current_phase(uvm_phase *phase);
    uvm_phase* set_current_phase(std::string phase);

    uvm_phase* add_phase(std::string name, uvm_phase_type type = UVM_PRERUN_PHASE, uvm_phase_order order = UVM_TOP_DOWN);
    void add_phase(uvm_phase* pphase);
    void add_arc(std::string from_phase, std::string to_phase, unsigned int priority = 0);
    void add_arc(uvm_phase* from_phase, uvm_phase* to_phase, unsigned int priority = 0);
    uvm_phase* get_phase(std::string name);
    void go_to_phase(std::string name);
    void go_to_phase(uvm_phase* phase);

    virtual void execute_schedule(uvm_component *pcomp = NULL);
    virtual void start_schedule(uvm_component *pcomp = NULL);
    virtual void init(void);
    virtual int execute_phase(std::string phase, uvm_phase_state state, sc_core::sc_module* pmod = NULL);
    virtual int execute_quasi_static_phase(std::string phase, uvm_phase_state state);

    void set_max_runtime(sc_core::sc_time time);
    void set_continue(bool bcontinue);
    virtual void start_of_simulation();

    void register_callback(uvm_component* pcomp);
    void wait_func();

protected:
    virtual void execute_nonruntime_phase(uvm_component *pcomp = NULL);
    virtual void execute_runtime_phase(uvm_component *pcomp = NULL);

    std::map<std::string, uvm_phase*> _phase_map;

    uvm_phase*     _top_phase;
    uvm_phase*     _next_phase;
    uvm_phase*     _current_phase;
    //uvm_event      _phase_end_ev;
    bool           _bcontinue;
    bool           _bsim_start;

    sc_core::sc_time  _max_runtime;
    sc_core::sc_event _sim_start_ev;
    
private:
    void wait_barrier(void);

};

}  // namespace

#endif // UVM_SCHEDULE_H



