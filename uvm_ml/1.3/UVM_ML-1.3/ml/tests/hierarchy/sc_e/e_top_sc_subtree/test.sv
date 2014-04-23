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

import uvm_pkg::*;
`include "uvm_macros.svh"
 import uvm_ml::*;

class svtop extends uvm_test;
    `uvm_component_utils(svtop)
    function new(string name, uvm_component parent=null);
        super.new(name, parent);
        $display("SV svtop::new ");
    endfunction
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        for (integer i = 0; i < 1000000; i++) begin
            uvm_ml::synchronize();
            #1;
        end    
        phase.drop_objection(this);
    endtask
endclass


module topmodule;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[2];
   
   tops[0] = "e:top.e";
   tops[1] = "SV:svtop";

   uvm_ml_run_test(tops, "");
end
`endif
endmodule
