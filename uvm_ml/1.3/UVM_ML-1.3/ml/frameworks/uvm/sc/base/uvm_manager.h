//----------------------------------------------------------------------
//   Copyright 2009 Cadence Design Systems, Inc.
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

/*! \file uvm_manager.h
  \brief Central manager of UVM-SC global functions.
*/

#ifndef UVM_MANAGER_H
#define UVM_MANAGER_H


#include "sysc/kernel/sc_event.h"
#include "sysc/kernel/sc_join.h"

//////////////

namespace uvm {

class uvm_component;

typedef enum {
  UVM_SC_STOP,
  UVM_NO_SC_STOP
} stop_mode_enum;

//------------------------------------------------------------------------------
//
// CLASS: uvm_manager
//
// Internal implementation class.
// Stores global settings, and implements most of the global functions.
// A singleton instance of this class is created for a given simulation run.
//
//------------------------------------------------------------------------------

/*! \class uvm_manager
  \brief Stores global settings, and implements most of the global functions.

  A singleton instance of this class is created for a given simulation run
*/
class uvm_manager {
public:

  friend class uvm_component;

  static uvm_manager* get_manager();
 
  void set_stop_mode(stop_mode_enum mode = UVM_SC_STOP);

  void set_global_timeout(sc_core::sc_time t);
  void set_global_stop_timeout(sc_core::sc_time t);
  
  void stop_request();

  uvm_component* find_component(const char* name);
  uvm_component* find_module(const char* name);
  std::vector<uvm_component*> find_all(const char* name = ".*");
  std::vector<uvm_component*> find_all_module(const char* name);

  unsigned int get_num_tops();
  void set_top(sc_core::sc_module* comp);
  std::vector<sc_core::sc_module*> get_tops();
  std::vector<uvm_component*>      get_uvm_component_tops();

protected:

  uvm_manager();
  ~uvm_manager();

  void wait_for_global_timeout();
  void wait_for_stop_timeout();

  void stop_spawner();
  void spawn_stop(sc_core::sc_module* mod);
  void end_run_phase();

  void do_kill_all();
  void do_kill(sc_core::sc_module* mod);
  
  void do_extract_all();
  void do_extract(sc_core::sc_module* mod);
  
  void do_check_all();
  void do_check(sc_core::sc_module* mod);
  
  void do_report_all();
  void do_report(sc_core::sc_module* mod);

protected:

  static uvm_manager* m_mgr;
         
  stop_mode_enum                   m_stop_mode;
  sc_core::sc_time                 m_global_timeout;
  sc_core::sc_time                 m_stop_timeout;
  sc_core::sc_join                 m_join_stop;
  std::vector<sc_core::sc_module*> m_tops;
};

inline
uvm_manager* get_uvm_manager() {
  return uvm_manager::get_manager();
}

} // namespace uvm

#endif
