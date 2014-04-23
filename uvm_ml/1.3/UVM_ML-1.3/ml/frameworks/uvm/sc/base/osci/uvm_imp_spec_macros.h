//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
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

/*! \file osci/uvm_imp_spec_macros.h
  \brief OS specific macro definitions.
*/
#ifndef UVM_ML_MACROS_H
#define UVM_ML_MACROS_H
#define MARK_THREAD_INVISIBLE(o)

#define SC_MAX_TIME sc_time(~sc_dt::UINT64_ZERO, false) 

#define RESET_PROC_EXTERN(proc)
#define SET_PROC_EXTERN(proc)

#undef UVM_DEFINE_MESSAGE
#define UVM_DEFINE_MESSAGE(id,unused,text) \
  namespace sc_core { extern const char id[] = text; }

#define CHECK_STOP_AT_PHASE_END() sc_get_curr_simcontext()->check_stop()

#define NODE_CONSTRUCTION_DONE(pmod) \
    uvm_component* comp = DCAST<uvm_component*>(pmod); \
    if (comp) \
        comp->build_phase(this); \
    sc_get_curr_simcontext()->quasi_static_module_construction_done(pmod); 

#define QUASI_STATIC_END_OF_CONSTRUCTION() sc_get_curr_simcontext()->quasi_static_end_of_construction();

#define NODE_CONNECT(pmod) { uvm_component* comp = DCAST<uvm_component*>(pmod); if (comp) comp->connect_phase(this); }

#define QUASI_STATIC_COMPLETE_BINDING() sc_get_curr_simcontext()->quasi_static_complete_binding()

#define NODE_END_OF_ELABORATION(pmod) \
    uvm_component* comp = DCAST<uvm_component*>(pmod); \
    if (comp) \
        comp->end_of_elaboration_phase(this); \
    else  \
        sc_get_curr_simcontext()->quasi_static_module_end_of_elaboration(pmod); 

#define QUASI_STATIC_END_OF_ELABORATION() sc_get_curr_simcontext()->quasi_static_end_of_elaboration();

#define NODE_START_OF_SIMULATION(pmod) \
    uvm_component* comp = DCAST<uvm_component*>(pmod); \
    if (comp) \
        comp->start_of_simulation_phase(this); \
    else \
        sc_get_curr_simcontext()->quasi_static_module_start_of_simulation(pmod);

#define QUASI_STATIC_START_OF_SIMULATION() sc_get_curr_simcontext()->quasi_static_start_of_simulation();

#define QUASI_STATIC_PREPARE_TO_SIMULATE() sc_get_curr_simcontext()->quasi_static_prepare_to_simulate();

#endif
