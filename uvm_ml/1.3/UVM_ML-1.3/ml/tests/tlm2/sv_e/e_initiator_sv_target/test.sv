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


//----------------------------------------------------------------------
// consumer
//----------------------------------------------------------------------
class consumer extends uvm_component;

    uvm_tlm_nb_target_socket #(consumer) target_socket;

    int unsigned transaction_count;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    `uvm_component_utils(consumer)

        function void build();
            target_socket = new("target_socket", this);
        endfunction

    function void connect();
    endfunction

    function uvm_tlm_sync_e nb_transport_fw(uvm_tlm_generic_payload t,
                                            ref uvm_tlm_phase_e p,
					    input uvm_tlm_time delay);
        uvm_tlm_sync_e res;
	$display("[SV ",$realtime,"] consumer received", t.convert2string());
        transaction_count++;
        return UVM_TLM_COMPLETED;
    endfunction

    function void report();
        if(transaction_count == 10)
            $display("** UVM TEST PASSED **");
        else
            $display("** UVM TEST FAILED **"); 
    endfunction

endclass

//----------------------------------------------------------------------
// env
//----------------------------------------------------------------------
class env extends uvm_component;

    `uvm_component_utils(env)

    consumer c;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build();
        c = new("consumer", this);
    endfunction

    function void phase_ended(uvm_phase phase);
        if (phase.get_name() == "build") begin
            uvm_ml::ml_tlm2 #()::register(c.target_socket);
        end
    endfunction

    function void connect();
        bit res;
        $display("Connecting the sockets");
        res = uvm_ml::connect("sys.producer.isocket", c.target_socket.get_full_name());
    endfunction

endclass

//----------------------------------------------------------------------
// test
//----------------------------------------------------------------------
class test extends uvm_component;

    `uvm_component_utils(test)

    env e;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build();
        e = new("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        for (integer i   = 0; i < 1000000; i++) begin
            uvm_ml::synchronize();
            #1;
        end    
        phase.drop_objection(this);
    endtask
endclass

module svtop;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[2];

   
   tops[0] = "sv:test";
   tops[1] = "e:top.e";

   uvm_ml_run_test(tops, "");
end // initial begin
`endif
endmodule
