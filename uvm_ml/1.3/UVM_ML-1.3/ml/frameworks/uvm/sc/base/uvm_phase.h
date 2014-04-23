//----------------------------------------------------------------------
//   Copyright 2012-2013 Advanced Micro Devices Inc.
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

/*! \file uvm_phase.h
  \brief Header file for UVM-SC phases.
*/
#ifndef UVM_PHASE_H
#define UVM_PHASE_H

#include <systemc.h>
#include <string>
#include <map>
#include <vector>
#include "base/uvm_callback.h"
#include "base/uvm_barrier.h"

namespace uvm {

class uvm_schedule;
class uvm_component;

enum uvm_phase_type
{
    UVM_PRERUN_PHASE,
    UVM_RUNTIME_PHASE,
    UVM_POSTRUN_PHASE    
};

enum uvm_phase_order
{
    UVM_TOP_DOWN,
    UVM_BOTTOM_UP,
    UVM_NA
};

enum uvm_phase_state
{
    UVM_PHASE_DORMANT,
    UVM_PHASE_READY_TO_START,
    UVM_PHASE_EXECUTING,
    UVM_PHASE_READY_TO_END,
    UVM_PHASE_ENDED,
    UVM_PHASE_DONE
};

enum uvm_sync_point
{
    UVM_SYNC_AT_START,
    UVM_SYNC_AT_END
};



//------------------------------------------------------------------------------
// Class: uvm_phase
//  Phase object
//------------------------------------------------------------------------------
//class uvm_phase : public sc_module
/*! \class uvm_phase
  \brief Phase object.

  
*/
class uvm_phase
{
public:
    uvm_phase(std::string name, uvm_schedule* p_schedule, uvm_phase_type type = UVM_PRERUN_PHASE, uvm_phase_order order = UVM_TOP_DOWN);
    virtual ~uvm_phase();

    uvm_phase_type get_phase_type();
    uvm_phase_order get_phase_order();
    uvm_phase_state get_phase_state();
    std::string get_name();

    void set_phase_state(uvm_phase_state state);

    void set_schedule (uvm_schedule *p_schedule);
    uvm_schedule * get_schedule();

    void add_next_phase(uvm_phase* phase, unsigned int priority);
    uvm_phase* get_next_phase();
    void go_to_phase(uvm_phase* phase);
    void go_to_phase(std::string name);
    void clear_next_phase_req();

    virtual void execute(sc_core::sc_module* pmod = NULL);
    virtual int start() { return 1; };
    virtual int end() { return 1; };


    void sync_phase(uvm_phase* phase, uvm_sync_point sync_point);
    bool is_ready_to_start();
    bool is_ready_to_end();

    uvm_callback_agent* get_callback_agent(uvm_phase_state state);

    void register_comp_callback(uvm_component* pcomp);

    uvm_barrier    barrier;

    bool is_sync_point_ready(uvm_sync_point sync_point);
    void wait_ready_to_start();
    void wait_ready_to_end();

    
protected:
    virtual void execute_runtime_phase();
    virtual void execute_nonruntime_phase(sc_core::sc_module* pmod = NULL);
    virtual void execute_topdown_phase(sc_core::sc_module* pmod);
    virtual void execute_bottomup_phase(sc_core::sc_module* pmod);

    virtual void process_state_executing_nonruntime(sc_core::sc_module* pmod);
    virtual void process_state_executing_runtime(uvm_component* pcomp);
    virtual void process_state_non_executing(uvm_component* pcomp);

    std::string      _name;
    uvm_phase_type   _type;
    uvm_phase_state  _state;
    uvm_phase_order  _order;
    uvm_schedule*    _pschedule;

    std::multimap<unsigned int, uvm_phase*> _next_phase_map;
    std::multimap<unsigned int, uvm_phase*> _next_phase_req_map;
    std::vector<uvm_phase *> _sync_at_start_phase_vec;
    std::vector<uvm_phase *> _sync_at_end_phase_vec;
    std::vector<uvm_component *> _comp_callback_vec;
    std::map<uvm_phase_state, uvm_callback_agent*> _callback_map;

    virtual int do_execute(sc_core::sc_module * pmod) { return 1; }

private:


    sc_core::sc_event ready_to_start_ev;

};

}  // namespace

#endif // UVM_PHASE_H
