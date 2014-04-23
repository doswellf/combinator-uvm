//----------------------------------------------------------------------
//   Copyright 2013 Advanced Micro Devices Inc.
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



//----------------------------------------------------------------------
// Class: uvm_ml_phase
// 
// ML phase functionality.
//----------------------------------------------------------------------
class uvm_ml_phase extends uvm_phase;

    //----- Public
    extern function new(string name="uvm_phase",
                        uvm_phase_type phase_type=UVM_PHASE_SCHEDULE,
                        uvm_phase parent=null);

    extern static task          process_phase_end(uvm_component comp, string phase_name, uvm_phase_state state);
    extern static task          ml_run_phases(uvm_component comp = null, bit bsequential_prerun = 0);
    extern static function bit  ml_do_nonblocking_phase (uvm_component comp, string phase_name, uvm_phase_state state);
    extern static function void ml_do_blocking_phase (uvm_component comp, string phase_name, uvm_phase_state state);

    static bit m_prepare_for_run_phases_started      = 0;
    static bit m_not_first_time_in_nonblocking_phase = 0;

    `uvm_object_utils(uvm_phase)

endclass

//-----------------------------------------------------------------------------
// Function: new
// 
//-----------------------------------------------------------------------------
function uvm_ml_phase::new(string name="uvm_phase",
                           uvm_phase_type phase_type=UVM_PHASE_SCHEDULE,
                           uvm_phase parent=null);
    super.new(name);

endfunction : new


//------------------------------------------------------------------------------
// Function: ml_run_phases
//
// This task is the ML version of the uvm_phase::m_run_phases() task.
//
// There are 2 additional arguments (comp & bsequential_prerun)
//
// 1. comp is passed into the uvm_phase::execute_phase task, if comp is not null
//    the execute_phase will only traverse from the top of comp, otherwise
//    it will traverse from uvm_root (default & non-ML behaviour).
//
// 2. When bsequential_prerun is set, this specified that this call is executing 
//    the prerun phases sequentially (do not fork or execute delta cycles).
//    It will execute the pre-run phases (the function phases) then return to 
//    the caller (phase master) after it hits the first task phase (run).
//
// The phase master, would procedurally call ml_run_phases() with 
// bsequential_prerun set.  After the call returns it will fork ml_run_phases
// with bsequential_prerun = 0 (executing the rest of the runtime phases and
// post-run phases).
//
// It was decided for ML, that pre-run phases should be executed sequentially.
// This allows phasing through all pre-run phases, before other run threads 
// get executed, this ensures all TB components are built and connected before
// TB execution.
//
// Parameters:
//
//  comp               - Component subtree to start executing the phase from
//  bsequential_prerun - Indicates if the pre-run phases should be executed
//                       sequentially or not.
//
//------------------------------------------------------------------------------
task uvm_ml_phase::ml_run_phases(uvm_component comp = null, bit bsequential_prerun = 0);
  uvm_task_phase task_phase;
  uvm_phase      phase;

  // initiate by starting first phase in common domain
  if (m_prepare_for_run_phases_started == 0)
  begin
      uvm_phase ph = uvm_domain::get_common_domain();
      void'(uvm_phase::ml_hopper_try_put(ph));
      m_prepare_for_run_phases_started = 1;
  end

  do begin
    uvm_phase::ml_hopper_get(phase);

    if (bsequential_prerun) begin
      phase.execute_phase(comp, 1);
    end
    else begin
      fork
          phase.execute_phase(comp, 0);
      join_none
      #0;  // let the process start running
    end

    uvm_phase::ml_hopper_peek(phase);
    if ($cast(task_phase, phase.m_imp) == 0)
        task_phase = null;

  end while (!bsequential_prerun || (task_phase == null));  // If bsequential_prerun, execute loop until the first task phase (run)

endtask : ml_run_phases


//------------------------------------------------------------------------------
// Function: ml_do_nonblocking_phase
//
// Called when SV is not the phase master and a phase notification is recieved
// to execute a nonblocking phase action (non-runtime phase execution, phase_
// start, phase_end, phase_ready_to_end)
// 
// When SV is a phase slave, it does not use the phase_hopper.  On a phase
// notification, if the phase is supported, it will execute that phase on the 
// 'comp' subtree that is passed in for non-runtime phases.  For runtime
// phases, the phase will traverse from uvm_root.
//
// Parameters:
//
//  comp            - Component subtree to start executing the phase from
//  phase_name      - Name of phase
//  uvm_phase_state - State the phase is in. ML does not use the full 
//                    range of uvm_phase_state.  Only uses the following 'actions'
//                    STARTED, EXECUTING, READY_TO_END and ENDED.
//
//------------------------------------------------------------------------------
function bit uvm_ml_phase::ml_do_nonblocking_phase(uvm_component comp, string phase_name, uvm_phase_state state);

    uvm_phase       phase;
    `uvm_ovm_(root) root_object;

    root_object = `uvm_ovm_(root)::get();

    if (!m_not_first_time_in_nonblocking_phase) begin
        m_not_first_time_in_nonblocking_phase = 1;
        uvm_objection::m_init_objections();
    end

    phase = root_object.get_phase_by_name(phase_name);
    if (phase != null)
        phase.ml_execute_phase(comp, state);

    // Do 'ending stuff' when the last phase is reached
    if ((phase_name == "final") && (state == UVM_PHASE_ENDED))
    begin
        fork 
            process_phase_end(comp, phase_name, state);
        join_none
    end

    return root_object.do_nonblocking_phase(phase_name);

endfunction : ml_do_nonblocking_phase

//------------------------------------------------------------------------------
// Function: ml_do_blocking_phase
//
// Called when SV is not the phase master and a phase notification is recieved
// to execute a runtime phase (action = EXECUTING)
// 
// When SV is a phase slave, it does not use the phase_hopper.  On a phase
// notification, if the phase is supported, it will execute that phase on the 
// 'comp' subtree that is passed in for non-runtime phases.  For runtime
// phases, the phase will traverse from uvm_root.
//
// Parameters:
//
//  comp            - Component subtree to start executing the phase from
//  phase_name      - Name of phase
//  uvm_phase_state - State the phase is in. ML does not use the full 
//                    range of uvm_phase_state.  Only uses the following 'actions'
//                    STARTED, EXECUTING, READY_TO_END and ENDED.
//
//------------------------------------------------------------------------------
function void uvm_ml_phase::ml_do_blocking_phase(uvm_component comp, string phase_name, uvm_phase_state state);

    bit             result;
    uvm_phase       phase;
    `uvm_ovm_(root) root_object;

    root_object = `uvm_ovm_(root)::get();

    phase = root_object.get_phase_by_name(phase_name);
    if (phase != null)
        phase.ml_execute_phase(comp, state);

    root_object.do_blocking_phase(phase_name);

endfunction : ml_do_blocking_phase

//------------------------------------------------------------------------------
// Function: process_phase_end
//
// Set m_phase_all_done, to notify root phasing/test ending.
//
// Parameters:
//
//  comp            - Component subtree to start executing the phase from
//  phase_name      - Name of phase
//  uvm_phase_state - State the phase is in. ML does not use the full 
//                    range of uvm_phase_state.  Only uses the following 'actions'
//                    STARTED, EXECUTING, READY_TO_END and ENDED.
//
//------------------------------------------------------------------------------
task uvm_ml_phase::process_phase_end(uvm_component comp, string phase_name, uvm_phase_state state);

    `uvm_ovm_(root) root_object;
    root_object = `uvm_ovm_(root)::get();

    root_object.m_phase_all_done = 1;
    void'(root_object.do_nonblocking_phase(phase_name));

endtask : process_phase_end







