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

//----------------------------------------------------------------------
// Class: uvm_ml_phase_service
//
// SV ML phase controller service.  
//
// This class extends uvm_component.  The SV ML phase service relies 
// on uvm_phase scheduler to notify it (via component phase callbacks) 
// of current phases.  When its phase callback is called, it will
// called the corresponding backplane API (notify_phase/notify_runtime_phase)
// to drive the phases for the other frameworks.
// 
//----------------------------------------------------------------------
class uvm_ml_phase_service extends uvm_component;

    //----- Singleton pointer
    static protected uvm_ml_phase_service uvm_ml_phase_service_inst;

    //----- Public
    extern function new (string name, uvm_component parent = null);

    extern static function uvm_ml_phase_service get_inst();

    extern task start_phasing();
    extern local task end_phasing();
    extern local task notify_runtime_phase_exec(uvm_phase phase);
    extern local function void notify_runtime_phase_nonexec(uvm_phase phase, uvm_ml_phase_action_e action);
    extern local function void notify_phase(uvm_phase phase, uvm_ml_phase_action_e action);
    extern function void srv_notify_phase_done(string phase_group, string phase_name);

    extern function void resolve_bindings();
    extern function void build_phase(uvm_phase phase);
    extern function void connect_phase(uvm_phase phase);
    extern function void end_of_elaboration_phase(uvm_phase phase);
    extern function void start_of_simulation_phase(uvm_phase phase);

    extern task run_phase(uvm_phase phase);
    extern task pre_reset_phase(uvm_phase phase);
    extern task reset_phase(uvm_phase phase);
    extern task post_reset_phase(uvm_phase phase);
    extern task pre_configure_phase(uvm_phase phase);
    extern task configure_phase(uvm_phase phase);
    extern task post_configure_phase(uvm_phase phase);
    extern task pre_main_phase(uvm_phase phase);
    extern task main_phase(uvm_phase phase);
    extern task post_main_phase(uvm_phase phase);
    extern task pre_shutdown_phase(uvm_phase phase);
    extern task shutdown_phase(uvm_phase phase);
    extern task post_shutdown_phase(uvm_phase phase);

    extern function void extract_phase(uvm_phase phase);
    extern function void check_phase(uvm_phase phase);
    extern function void report_phase(uvm_phase phase);
    extern function void final_phase(uvm_phase phase);

    extern function void phase_started(uvm_phase phase);
    extern function void phase_ready_to_end(uvm_phase phase);
    extern function void phase_ended(uvm_phase phase);

    `uvm_component_utils(uvm_ml_phase_service)
endclass

//--- Create the singleton
static uvm_ml_phase_service uvm_ml_phase_service_mgr = null;

//-----------------------------------------------------------------------------
// Function: get_inst
// 
// Get pointer to the uvm_ml_phase_service singleton.
//
//-----------------------------------------------------------------------------
function uvm_ml_phase_service uvm_ml_phase_service::get_inst();
      if (uvm_ml_phase_service_inst == null)
        uvm_ml_phase_service_inst = uvm_ml_phase_service::type_id::create("uvm_ml_phase_service_inst", uvm_top);

    return uvm_ml_phase_service_inst;
endfunction : get_inst

//-----------------------------------------------------------------------------
// Function: new
// 
//-----------------------------------------------------------------------------
function uvm_ml_phase_service::new (string name, uvm_component parent = null);
    super.new(name, parent);
endfunction : new

//-----------------------------------------------------------------------------
// Task: start_phasing
// 
// Called by the backplane to start the ML phasing.
//
// It was decided for ML, that pre-run phases should be executed sequentially.
// This allows phasing through all pre-run phases, before other run threads 
// get executed, this ensures all TB components are built and connected before
// TB execution.  
//
// This method will procedurally call ml_run_phases() with bsequential_prerun = 1.
// Once ml_run_phases() returns (all pre-run phases have finished), it will 
// fork ml_run_phases(), leaving bsequential_prerun = 0.
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::start_phasing();

    uvm_objection::m_init_objections();

    // Phase until the end of pre-run
    uvm_ml_phase::ml_run_phases(this, 1);

    // Phase the rest of the phases
    fork
        uvm_ml_phase::ml_run_phases(this);
        end_phasing();
    join_none

endtask : start_phasing

//-----------------------------------------------------------------------------
// Task: end_phasing
// 
// Wait until phasing has ended and do 'test ending stuff'.
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::end_phasing();
    `uvm_ovm_(root) root_object;
    root_object = `uvm_ovm_(root)::get();

    #0;     // wait for phasing to start
    wait(root_object.m_phase_all_done == 1);

    root_object.end_test();
endtask : end_phasing


//-----------------------------------------------------------------------------
// Function: build_phase
// 
// Component build_phase() callback.  Call local method <notify_phase> which
// will call backplane API bp_notify_phase() to notify other framework
// build_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::build_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : build_phase

//-----------------------------------------------------------------------------
// Function: connect_phase
// 
// Component connect_phase() callback.  Call local method <notify_phase> which
// will call backplane API bp_notify_phase() to notify other framework
// connect_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::connect_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : connect_phase

//-----------------------------------------------------------------------------
// Function: resovle_bindings
// 
// Call backplane API bp_notify_phase() to notify other framework
// resolve_bindings is starting execution.
// 
// resolve_bindings is a special phase.  It is not part of the uvm_phase.
// Directly call bp_notify_phase_done
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::resolve_bindings();
    void'(uvm_ml_notify_phase("common", "resolve_bindings", UVM_ML_PHASE_EXECUTING)); 
endfunction : resolve_bindings

//-----------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// 
// Component end_of_elaboration_phase() callback.  Call local method <notify_phase> which
// will call backplane API bp_notify_phase() to notify other framework
// end_of_elaboration_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::end_of_elaboration_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : end_of_elaboration_phase

//-----------------------------------------------------------------------------
// Function: start_of_simulation_phase
// 
// Component start_of_simulation_phase() callback.  Call local method <notify_phase> which
// will call backplane API bp_notify_phase() to notify other framework
// start_of_simulation_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::start_of_simulation_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : start_of_simulation_phase

//-----------------------------------------------------------------------------
// Task: run_phase
// 
// Component run_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// run_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::run_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : run_phase

//-----------------------------------------------------------------------------
// Task: pre_reset_phase
// 
// Component pre_reset_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// pre_reset_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::pre_reset_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : pre_reset_phase

//-----------------------------------------------------------------------------
// Task: reset_phase
// 
// Component reset_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// reset_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::reset_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : reset_phase

//-----------------------------------------------------------------------------
// Task: post_reset_phase
// 
// Component post_reset_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// post_reset_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::post_reset_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : post_reset_phase

//-----------------------------------------------------------------------------
// Task: pre_configure_phase
// 
// Component pre_configure_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// pre_configure_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::pre_configure_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : pre_configure_phase

//-----------------------------------------------------------------------------
// Task: configure_phase
// 
// Component configure_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// configure_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::configure_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : configure_phase

//-----------------------------------------------------------------------------
// Task: post_configure_phase
// 
// Component post_configure_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// post_configure_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::post_configure_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : post_configure_phase

//-----------------------------------------------------------------------------
// Task: pre_main_phase
// 
// Component pre_main_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// pre_main_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::pre_main_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : pre_main_phase

//-----------------------------------------------------------------------------
// Task: main_phase
// 
// Component main_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// main_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::main_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : main_phase

//-----------------------------------------------------------------------------
// Task: post_main_phase
// 
// Component post_main_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// post_main_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::post_main_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : post_main_phase

//-----------------------------------------------------------------------------
// Task: pre_shutdown_phase
// 
// Component pre_shutdown_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// pre_shutdown_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::pre_shutdown_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : pre_shutdown_phase

//-----------------------------------------------------------------------------
// Task: shutdown_phase
// 
// Component shutdown_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// shutdown_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::shutdown_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : shutdown_phase

//-----------------------------------------------------------------------------
// Task: post_shutdown_phase
// 
// Component post_shutdown_phase() callback.  Call local method <notify_runtime_phase_exec>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// post_shutdown_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::post_shutdown_phase(uvm_phase phase);
    notify_runtime_phase_exec(phase);
endtask : post_shutdown_phase


//-----------------------------------------------------------------------------
// Function: extract_phase
// 
// Component extract_phase() callback.  Call local method <notify_phase>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// extract_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::extract_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : extract_phase

//-----------------------------------------------------------------------------
// Function: check_phase
// 
// Component check_phase() callback.  Call local method <notify_phase>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// check_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::check_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : check_phase

//-----------------------------------------------------------------------------
// Function: report_phase
// 
// Component report_phase() callback.  Call local method <notify_phase>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// report_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::report_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : report_phase

//-----------------------------------------------------------------------------
// Function: final_phase
// 
// Component final_phase() callback.  Call local method <notify_phase>
// which will call backplane API bp_notify_runtime_phase() to notify other framework
// final_phase is starting execution.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::final_phase(uvm_phase phase);
    notify_phase(phase, UVM_ML_PHASE_EXECUTING);
endfunction : final_phase

//-----------------------------------------------------------------------------
// Function: phase_started
// 
// Component phase_started() callback.  Call local method 
// <notify_runtime_phase_nonexec> if phase is a runtime phase otherwise
// call <notify_phase>.  Local methods will call the appropriate backplane
// API to notify phase is 'starting'.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::phase_started(uvm_phase phase);
    uvm_task_phase task_phase;
    uvm_root root = uvm_root::get();

    if (phase.get_name() == "end_of_elaboration")
    begin
        void'(uvm_ml_notify_phase("common", "resolve_bindings", UVM_ML_PHASE_STARTED)); 
        root.phase_started(phase);
        void'(uvm_ml_notify_phase("common", "resolve_bindings", UVM_ML_PHASE_ENDED)); 
    end

    // If phase is a task phase, then it's a runtime phase
    if ($cast(task_phase, phase.m_imp))
        notify_runtime_phase_nonexec(phase, UVM_ML_PHASE_STARTED);
    else
        notify_phase(phase, UVM_ML_PHASE_STARTED);
endfunction : phase_started

//-----------------------------------------------------------------------------
// Function: phase_ready_to_end
// 
// Component phase_ready_to_end() callback.  Call local method 
// <notify_runtime_phase_nonexec> if phase is a runtime phase otherwise
// call <notify_phase>.  Local methods will call the appropriate backplane
// API to notify phase is ready_to_end.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::phase_ready_to_end(uvm_phase phase);
    uvm_task_phase task_phase;

    // TODO: Is phase_ready_to_end only called for runtime phase?
    if ($cast(task_phase, phase.m_imp))
        notify_runtime_phase_nonexec(phase, UVM_ML_PHASE_READY_TO_END);
    else
        notify_phase(phase, UVM_ML_PHASE_READY_TO_END);
endfunction : phase_ready_to_end


//-----------------------------------------------------------------------------
// Function: phase_ended
// 
// Component phase_ended() callback.  Call local method 
// <notify_runtime_phase_nonexec> if phase is a runtime phase otherwise
// call <notify_phase>.  Local methods will call the appropriate backplane
// API to notify phase is phase_ended.
//
// Parameters:
//
//  phase - ptr to phase
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::phase_ended(uvm_phase phase);
    uvm_task_phase task_phase;

    if ($cast(task_phase, phase.m_imp))
        notify_runtime_phase_nonexec(phase, UVM_ML_PHASE_ENDED);
    else
        notify_phase(phase, UVM_ML_PHASE_ENDED);
endfunction : phase_ended


//-----------------------------------------------------------------------------
// Function: notify_phase
// 
// Call backplane API bp_notify_phase() to notify the other frameworks of
// 'phase' and 'action'.
//
// Parameters:
//
//  phase  - ptr to phase
//  action - Current phase action (eg. START, EXECUTING, READY_TO_END, ENDED)
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::notify_phase(uvm_phase phase, uvm_ml_phase_action_e action);
    uvm_domain domain    = phase.get_domain();

    void'(uvm_ml_notify_phase(domain.get_name(), phase.get_name(), action)); 

endfunction : notify_phase

//-----------------------------------------------------------------------------
// Task: notify_runtime_phase_exec
// 
// Call backplane API bp_notify_runtime_phase() to notify the other frameworks of
// 'phase'.
//
// Checks the output variable 'participate', which indicates the number of 
// frameworks particpating in this phase.  Raise the phase_done objection for 
// this phase to the participating framework count. 
//
// When the other frameworks are ready to exit this phase, it will notify the backplane
// via bp_notify_phase_done().  Backplane will then call this controller's
// <srv_notify_phase_done> method.  The <srv_notify_phase_done> method will
// then call drop_objection().
//
// This class represents the other frameworks.  So when all frameworks are done
// 'participating' in a phase, the objection count for this class should be 0.
//
//
// Parameters:
//
//  phase  - ptr to phase
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_service::notify_runtime_phase_exec(uvm_phase phase);
    int unsigned   participate = 0;
    uvm_domain     domain      = phase.get_domain();

    void'(uvm_ml_notify_runtime_phase(domain.get_name(), phase.get_name(), UVM_ML_PHASE_EXECUTING, participate)); 

    if (participate > 0)
        phase.raise_objection(this, "notify_runtime_phase", participate);

endtask : notify_runtime_phase_exec

//-----------------------------------------------------------------------------
// Function: notify_runtime_phase_nonexec
// 
// Call backplane API bp_notify_runtime_phase() to notify the other frameworks of
// 'phase' and 'action'.
//
// Parameters:
//
//  phase  - ptr to phase
//  action - Current phase action (eg. START, EXECUTING, READY_TO_END, ENDED)
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::notify_runtime_phase_nonexec(uvm_phase phase, uvm_ml_phase_action_e action);
    int unsigned participate = 0;
    uvm_domain   domain = phase.get_domain();

    void'(uvm_ml_notify_runtime_phase(domain.get_name(), phase.get_name(), action, participate)); 

endfunction : notify_runtime_phase_nonexec


//-----------------------------------------------------------------------------
// Function: srv_notify_phase_done
// 
// When the other frameworks are ready to exit a phase, it will notify the backplane
// via bp_notify_phase_done().  Backplane will then call this method, which will
// drop the objection to the corresponding phase.
// 
// This class represents the other frameworks.  So when all frameworks are done
// 'participating' in a phase, the objection count for this class should be 0.
//
// Parameters:
//
//  phase_group - Name of group/domain the phase belongs to
//  phase_name  - Name of phase
//-----------------------------------------------------------------------------
function void uvm_ml_phase_service::srv_notify_phase_done(string phase_group, string phase_name);
    uvm_domain domain;
    uvm_phase  phase;

    if (phase_group == "common")
        domain = uvm_domain::get_common_domain();
    else
        domain = uvm_domain::get_uvm_domain();

    phase = domain.find_by_name(phase_name);
    if (phase != null)
        phase.drop_objection(this);
    else
        uvm_report_warning("PHMSTRSRVDONE", {"Phase ", phase_name, "is not found in domain ", phase_group}, UVM_NONE);

endfunction : srv_notify_phase_done

