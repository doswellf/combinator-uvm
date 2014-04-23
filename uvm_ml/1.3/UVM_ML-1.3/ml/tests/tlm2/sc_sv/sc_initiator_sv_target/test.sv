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
       uvm_tlm_generic_payload expected;
       uvm_tlm_sync_e res;
       $display("[SV ",$realtime," ns] consumer received", t.convert2string());
       expected = create_trans(transaction_count);
       check_data(expected,t);
       transaction_count++;
       res = target_socket.nb_transport_bw(t,p,delay);    
       return res;
    endfunction

      
   function void check_data(uvm_tlm_generic_payload expected,  uvm_tlm_generic_payload actual);
      
      byte unsigned d[];
      byte unsigned ed[];
      
      if(expected.get_address() != actual.get_address()) begin
	 $display("expected address ",expected.get_address()," actual address is ",actual.get_address());
	 assert(0);
      end
      
      if(expected.get_command() != actual.get_command()) begin
	 $display("expected command ",expected.get_command()," actual command is ",actual.get_command());
	 assert(0);
      end

       if(expected.get_data_length() != actual.get_data_length()) begin
	 $display("expected data_length ",expected.get_data_length()," actual data_length is ",actual.get_data_length());
	 assert(0);
       end
      
      expected.get_data(ed);
      actual.get_data(d);
      if(ed != d) begin
	 $display("expected data[0] ",ed[0]," actual data[0] is ",d[0]);
	 assert(0);
      end
      
   endfunction // check_that
   
   function uvm_tlm_generic_payload create_trans(int unsigned base);
      byte unsigned data[];
      uvm_tlm_generic_payload gp = new();
      
      data = new[base+1];
      for(int unsigned i = 0; i < base+1; i++) begin
	 data[i] = i;
      end
      
      gp.set_address(base*1000+base*100+base*10+base);
      gp.set_data_length(base+1);
      gp.set_data(data);
      gp.set_command(UVM_TLM_WRITE_COMMAND);
      
      return gp;
   endfunction // create_trans
   
    function void report();
        if(transaction_count == 10)
            $display("** UVM TEST PASSED **");
        else
            $display("** UVM TEST FAILED **"); 
       assert(transaction_count == 10);
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
        res = uvm_ml::connect("top.initiator.isocket", c.target_socket.get_full_name());
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

module top1;
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[1];

   
   tops[0] = "SC:top";

   uvm_ml_run_test(tops, "SV:test");
end // initial begin
`endif
endmodule
