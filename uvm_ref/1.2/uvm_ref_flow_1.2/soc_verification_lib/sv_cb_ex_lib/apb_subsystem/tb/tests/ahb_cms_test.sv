/*-------------------------------------------------------------------------
File name   : ahb_cms_test.sv
Title       : Test Case
Project     :
Created     :
Description : AHB Compliance Management test
Notes       : The test creates a apb_subsystem_tb and sets the default
            : sequence for the sequencer as apb_ss_cms_seq
----------------------------------------------------------------------*/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
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

class ahb_cms_test extends uvm_test;
   
   `uvm_component_utils(ahb_cms_test)

   apb_subsystem_tb ve;
   
   uvm_table_printer printer;

   function new(string name = "ahb_cms_test", uvm_component parent);
      super.new(name, parent);
      printer = new();
   endfunction
   
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   
    uvm_config_db#(uvm_object_wrapper)::set(this, "ve.virtual_sequencer.run_phase",
          "default_sequence", apb_ss_cms_seq::type_id::get());

    set_type_override("ahb_master_monitor", "ahb_monitor");
    super.build_phase(phase);
    ve = apb_subsystem_tb::type_id::create("ve", this);
   endfunction
   
endclass
