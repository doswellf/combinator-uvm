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

/*! \file uvm_common_phase.h
  \brief UVM-ML phasing.
*/
#ifndef UVM_COMMON_PHASE_H
#define UVM_COMMON_PHASE_H

#include <systemc.h>
#include "base/uvm_phase.h"

namespace uvm {



//------------------------------------------------------------------------------
// Class: uvm_common_phase
//  Phase object
//------------------------------------------------------------------------------
/*! \class uvm_common_phase
  \brief Phase object.

  
*/
class uvm_common_phase : public uvm_phase
{
public:
    uvm_common_phase(std::string name, uvm_schedule* p_schedule, uvm_phase_type type = UVM_PRERUN_PHASE, uvm_phase_order = UVM_TOP_DOWN);
    ~uvm_common_phase();

    virtual int do_execute(sc_core::sc_module * pmod) { return 1; };

protected:
    void process_state_executing_runtime(uvm_component* pcomp = NULL);
    void process_state_executing_nonruntime(sc_core::sc_module * pmod = NULL);

};

/*! \class uvm_build_phase
  \brief Build phase.

  
*/
class uvm_build_phase: public uvm_common_phase {

public:
    uvm_build_phase(uvm_schedule* p_schedule) : uvm_common_phase("build", p_schedule, UVM_PRERUN_PHASE, UVM_TOP_DOWN) {};

    virtual int do_execute(sc_core::sc_module* pmod);
    virtual int end();
};

/*! \class uvm_connect_phase
  \brief Connect phase.

  
*/
class uvm_connect_phase: public uvm_common_phase {

public:
    uvm_connect_phase(uvm_schedule* p_schedule) : uvm_common_phase("connect", p_schedule, UVM_PRERUN_PHASE, UVM_BOTTOM_UP) {};

    virtual int do_execute(sc_core::sc_module* pmod);
};

/*! \class uvm_end_of_elaboration_phase
  \brief End of elaboration phase.

  
*/
class uvm_end_of_elaboration_phase: public uvm_common_phase {

public:
    uvm_end_of_elaboration_phase(uvm_schedule* p_schedule) : uvm_common_phase("end_of_elaboration", p_schedule, UVM_PRERUN_PHASE, UVM_BOTTOM_UP) {};

    virtual int do_execute(sc_core::sc_module* pmod);
    virtual int end();
};

/*! \class uvm_start_of_simulation_phase
  \brief Start of simulation phase.

  
*/
class uvm_start_of_simulation_phase: public uvm_common_phase {

public:
    uvm_start_of_simulation_phase(uvm_schedule* p_schedule) : uvm_common_phase("start_of_simulation", p_schedule, UVM_PRERUN_PHASE, UVM_BOTTOM_UP) {};

    virtual int do_execute(sc_core::sc_module* pmod);
    virtual int end();
};

/*! \class uvm_run_phase
  \brief Run phase.

  
*/
class uvm_run_phase: public uvm_common_phase {

public:
    uvm_run_phase(uvm_schedule* p_schedule) : uvm_common_phase("run", p_schedule, UVM_RUNTIME_PHASE, UVM_NA) {};

    virtual int start();
};

}  // namespace

#endif // UVM_COMMON_PHASE_H
