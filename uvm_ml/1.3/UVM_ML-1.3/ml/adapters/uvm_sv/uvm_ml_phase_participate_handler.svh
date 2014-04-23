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
// Class: uvm_ml_phase_participate_handler
//
// Used only when SV is NOT the phase master.
// Class for handling phase_done notifications to the phase master.
//
// When a runtime notification is received for a phase, the SV adapter
// will set the participate variable to be 1 and create an instance of this 
// class and call the instance's execute method.  This method will 
// fork a process that waits for the phase_done objection for that
// phased to be all_dropped. When all objections are dropped  will call 
// the backplane API bp_notify_phase_done() to indicate that it is ready to 
// exit this phase.
//
//----------------------------------------------------------------------
class uvm_ml_phase_participate_handler;

  extern function      new(string name, string group);
  extern function void execute();
  extern task          check_objection();

  local string m_phase_name;        // Name of the phase
  local string m_phase_group;       // Name of the group/domain the phase belongs to

endclass


//-----------------------------------------------------------------------------
// Function: new
//
// Parameters:
//
//  name  - Name of the phase this class is monitoring
//  group - Name of the group/domain the phase belongs to
// 
//-----------------------------------------------------------------------------
function uvm_ml_phase_participate_handler::new(string name, string group);
    m_phase_name  = name;
    m_phase_group = group;
endfunction

//-----------------------------------------------------------------------------
// Function: execute
// 
// Forks a process that will wait for the phase_done objections to be 
// all_dropped.  The forking is done in this class instance rather than 
// directly in the export_notify_runtime_phase() because the fork is not
// 'processed' immediately, and subsequent export_notify_runtime_phase() calls
// overwrites the stack, causing invalid phase name/group in the fork process.
//
//-----------------------------------------------------------------------------
function void uvm_ml_phase_participate_handler::execute();
    fork
        check_objection();
    join_none
endfunction : execute

//-----------------------------------------------------------------------------
// Task: check_objection
// 
// If the phase has active objections, then wait until all objections are
// dropped.  Call bp_notify_phase_done() when there are no objections for
// the phase.
//
//-----------------------------------------------------------------------------
task uvm_ml_phase_participate_handler::check_objection();

    uvm_domain    domain;
    uvm_phase     phase;
    uvm_objection objection;

    #0; // allow runtime phases to execute before checking objections

    if (m_phase_group == "common")
        domain = uvm_domain::get_common_domain();
    else
       domain = uvm_domain::get_uvm_domain();

    phase     = domain.find_by_name(m_phase_name);
    objection = phase.get_objection();

    if (objection.get_objection_total() > 0)
        objection.wait_for(UVM_ALL_DROPPED);

    uvm_ml_notify_phase_done(m_phase_group, m_phase_name);

endtask : check_objection






