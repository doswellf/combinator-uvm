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

// Test demonstrates configuration across unified hierarchy
// e is the top component and it creates an SV subtree from its env

import uvm_pkg::*;
`include "uvm_macros.svh"
import uvm_ml::*;
`include "dt.sv"

  class env extends uvm_env;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV env::new %s", name);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      $display("SV env::build");
    endfunction
   
    `uvm_component_utils(env)

  endclass 
  
  // Test instantiates the "env"
  class test extends uvm_env;
    env sv_env;
    bit result;

    uvm_object tmp_obj; 
    data conf_data;
    pdata conf_pdata; 

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV test::new %s", get_full_name());
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);      
      $display("SV test::build %s", get_full_name());
       
      void'(get_config_object("conf_data",tmp_obj));
       
      assert($cast(conf_data,tmp_obj)!=0);
      assert(conf_data.addr == 10);
      assert(conf_data.trailer == 20);
      assert(conf_data.txt == "config object msg");

      void'(get_config_int("conf_pdata",conf_pdata));
       
      assert(conf_pdata.data == 30);
      assert(conf_pdata.addr == 4);
      assert(conf_pdata.payload == 50);
       
      sv_env = new("sv_env", this);
    endfunction
      
    task run_phase(uvm_phase phase);
      $display("SV test::run_phase %s", get_full_name());
    endtask
   
    `uvm_component_utils(test)
  endclass   

module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];
   
   tops[0] = "e:top.e";
   
   uvm_ml_run_test(tops, "");
end
`endif
endmodule
