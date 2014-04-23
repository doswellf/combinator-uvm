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

/*! \file uvm_common_schedule.cpp
  \brief Common schedule object.
*/
#define SC_INCLUDE_DYNAMIC_PROCESSES
#include "base/uvm_common_schedule.h"
#include "base/uvm_common_phase.h"
#include "base/uvm_globals.h"
#include "base/uvm_component.h"


namespace uvm {

using std::string;

uvm_common_schedule* uvm_common_schedule::_uvm_common_schedule = 0;
uvm_common_schedule* uvm_common_schedule::_uvm_schedule = 0;

//------------------------------------------------------------------------------
// Constructor: uvm_common_schedule
//------------------------------------------------------------------------------
uvm_common_schedule::uvm_common_schedule(sc_module_name name) :
    uvm_schedule(name)
{
}

//------------------------------------------------------------------------------
// Destructor: uvm_schedule
//------------------------------------------------------------------------------
uvm_common_schedule::~uvm_common_schedule()
{
}

uvm_common_schedule* uvm_common_schedule::get_uvm_common_schedule()
{
    uvm_phase* pphase;

    if (_uvm_common_schedule == 0)
    {
        _uvm_common_schedule = new uvm_common_schedule("common");

        pphase = new uvm_build_phase(_uvm_common_schedule);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_connect_phase(_uvm_common_schedule);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_end_of_elaboration_phase(_uvm_common_schedule);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_start_of_simulation_phase(_uvm_common_schedule);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_run_phase(_uvm_common_schedule);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_common_phase("extract", _uvm_common_schedule, UVM_POSTRUN_PHASE, UVM_BOTTOM_UP);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_common_phase("check", _uvm_common_schedule, UVM_POSTRUN_PHASE, UVM_BOTTOM_UP);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_common_phase("report", _uvm_common_schedule, UVM_POSTRUN_PHASE, UVM_BOTTOM_UP);
        _uvm_common_schedule->add_phase(pphase);

        pphase = new uvm_common_phase("final", _uvm_common_schedule, UVM_POSTRUN_PHASE, UVM_TOP_DOWN);
        _uvm_common_schedule->add_phase(pphase);

        _uvm_common_schedule->set_top_phase("build");
        //_uvm_common_schedule->set_top_phase("run");
        _uvm_common_schedule->add_arc("build", "connect");
        _uvm_common_schedule->add_arc("connect", "end_of_elaboration");
        _uvm_common_schedule->add_arc("end_of_elaboration", "start_of_simulation");
        _uvm_common_schedule->add_arc("start_of_simulation", "run");
        _uvm_common_schedule->add_arc("run", "extract");
        _uvm_common_schedule->add_arc("extract", "check");
        _uvm_common_schedule->add_arc("check", "report");
        _uvm_common_schedule->add_arc("report", "final");

    }

    return _uvm_common_schedule;

}


uvm_common_schedule* uvm_common_schedule::get_uvm_schedule()
{
    uvm_phase* pphase;
    uvm_phase* preset_phase;
    uvm_phase* pshutdown_phase;
    uvm_phase* prun_phase;
    uvm_common_schedule* pcommon_schedule;

    if (_uvm_schedule == 0)
    {
        _uvm_schedule = new uvm_common_schedule("uvm");

        preset_phase = new uvm_common_phase("reset", _uvm_schedule, UVM_RUNTIME_PHASE, UVM_NA);
        _uvm_schedule->add_phase(preset_phase);

        pphase = new uvm_common_phase("configure", _uvm_schedule, UVM_RUNTIME_PHASE, UVM_NA);
        _uvm_schedule->add_phase(pphase);

        pphase = new uvm_common_phase("main", _uvm_schedule, UVM_RUNTIME_PHASE, UVM_NA);
        _uvm_schedule->add_phase(pphase);

        pshutdown_phase = new uvm_common_phase("shutdown", _uvm_schedule, UVM_RUNTIME_PHASE, UVM_NA);
        _uvm_schedule->add_phase(pshutdown_phase);

        pcommon_schedule = get_uvm_common_schedule();
        prun_phase = pcommon_schedule->get_phase("run");

        preset_phase->sync_phase(prun_phase, UVM_SYNC_AT_START);
        pshutdown_phase->sync_phase(prun_phase, UVM_SYNC_AT_END);
        prun_phase->sync_phase(pshutdown_phase, UVM_SYNC_AT_END);

        _uvm_schedule->set_top_phase("reset");
        _uvm_schedule->add_arc("reset", "configure");
        _uvm_schedule->add_arc("configure", "main");
        _uvm_schedule->add_arc("main", "shutdown");

    }

    return _uvm_schedule;

}


void uvm_common_schedule::init(void)
{
    if (_top_phase == NULL)
    {
        cout << "uvm_common_schedule::init - top phase not set for schedule - " << name() << endl;
        exit(1);
    }

    _current_phase = _top_phase;
    _current_phase->set_phase_state(UVM_PHASE_READY_TO_START);


int num = 5;

}

void uvm_common_schedule::execute_build(uvm_component* pcomp)
{
    if (_current_phase->get_name()  != "build") 
    {
        cout << "ERROR:execute_build - first phase is not build" << endl;
        exit(1);
    }

    _current_phase->set_phase_state(UVM_PHASE_EXECUTING);
    _current_phase->execute(pcomp);
    _current_phase->set_phase_state(UVM_PHASE_DONE);
    _current_phase = _current_phase->get_next_phase();

    if (_bcontinue)
        sc_spawn(sc_bind(&uvm_schedule::start_schedule, this, pcomp));
}

} // namespace




