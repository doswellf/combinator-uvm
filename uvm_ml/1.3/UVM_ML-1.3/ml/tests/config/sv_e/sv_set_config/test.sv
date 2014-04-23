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

// Test demonstrates hierarchical construction
// SV is the top component and it creates an e subtree from its env

import uvm_pkg::*;
`include "uvm_macros.svh"
 import uvm_ml::*;
`include "dt.sv"

  class env extends uvm_env;

    uvm_component etop;

    data d;
    pdata pd;
      
    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV env::new %s", name);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      $display("SV env::build");
       
      d = new;
      d.addr = 10;
      d.trailer = 20;
      d.txt = "config object message";

      set_config_object("my_unit","conf_data",d);
      
      pd.data = 30;
      pd.addr = 4;
      pd.payload = 50;
        
      set_config_int("my_unit","conf_pdata",pd);
       
      // create ML junction node in e
      etop = uvm_ml_create_component("e", "my_unit", "my_unit", this);
    endfunction // build_phase
         
    task run_phase (uvm_phase phase);
      phase.raise_objection(this);
      #5000;
      phase.drop_objection(this);
    endtask
     
    `uvm_component_utils(env)

  endclass 
  
  // Test instantiates the "env"
  class test extends uvm_env;
    env sv_env;
    bit result;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV test::new %s", get_full_name());
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      $display("SV test::build %s", get_full_name());
      sv_env = new("sv_env", this);
    endfunction
   
    `uvm_component_utils(test)
  endclass    

module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];
   
   tops[0] = "SV:test";
   
   uvm_ml_run_test(tops, "");
end
`endif   
endmodule
