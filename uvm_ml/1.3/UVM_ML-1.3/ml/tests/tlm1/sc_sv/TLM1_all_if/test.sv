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
module topmodule;
 import uvm_ml::*;
 import uvm_pkg::*;  
`include "uvm_macros.svh"

`include "packet.sv"
`include "producer.sv"
`include "consumer.sv"

class test extends uvm_test;

  producer #(packet) p;
  consumer #(packet) c;

  `uvm_component_utils(test)

  function new (string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV test::new()");
  endfunction

  function void build();   
      $display("SV build() ");
      p = new("producer",this);
      c = new("consumer",this);
  endfunction

  function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") begin
          uvm_ml::ml_tlm1 #(packet)::register(p.put_port1);
          uvm_ml::ml_tlm1 #(packet)::register(p.put_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.get_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.peek_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.trans_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.put_nb_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.get_nb_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.peek_nb_port);
          uvm_ml::ml_tlm1 #(packet)::register(p.a_port);
          uvm_ml::ml_tlm1 #(packet)::register(c.put_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.get_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.peek_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.trans_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.put_nb_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.get_nb_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.peek_nb_export);
          uvm_ml::ml_tlm1 #(packet)::register(c.a_export);
      end
  endfunction

  function void connect();
      bit res;
      $display("SV connect() ");
      res = uvm_ml::connect(p.put_port1.get_full_name(), "sctop.prod.put_export");
      res = uvm_ml::connect(p.put_port.get_full_name(), "sctop.cons.put_export");
      res = uvm_ml::connect(p.get_port.get_full_name(), "sctop.cons.get_export");
      res = uvm_ml::connect(p.peek_port.get_full_name(), "sctop.cons.peek_export");
      res = uvm_ml::connect(p.trans_port.get_full_name(), "sctop.cons.trans_export");
      res = uvm_ml::connect(p.put_nb_port.get_full_name(), "sctop.cons.put_nb_export");
      res = uvm_ml::connect(p.get_nb_port.get_full_name(), "sctop.cons.get_nb_export");
      res = uvm_ml::connect(p.peek_nb_port.get_full_name(), "sctop.cons.peek_nb_export");
      res = uvm_ml::connect(p.a_port.get_full_name(), "sctop.cons.a_export");
      res = uvm_ml::connect("sctop.prod.put_port", c.put_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.get_port", c.get_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.peek_port", c.peek_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.trans_port", c.trans_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.put_nb_port", c.put_nb_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.get_nb_port", c.get_nb_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.peek_nb_port", c.peek_nb_export.get_full_name());
      res = uvm_ml::connect("sctop.prod.a_port", c.a_export.get_full_name());
  endfunction

  function void report();
      $display("SV report()");
     assert(c.check_sum==11);
  endfunction // void
   
   task run_phase(uvm_phase phase);
      packet p;
      for (integer i = 0; i < 1000; i++) begin
         uvm_ml::synchronize();
	 #1;
      end;
      $finish();      
   endtask // run_phase

endclass // test
`ifdef USE_UVM_ML_RUN_TEST
initial begin
   string tops[2];

   
   tops[0] = "SC:sctop";
   tops[1] = "SV:test";
   
   uvm_ml_run_test(tops, "");
end
`endif
endmodule


