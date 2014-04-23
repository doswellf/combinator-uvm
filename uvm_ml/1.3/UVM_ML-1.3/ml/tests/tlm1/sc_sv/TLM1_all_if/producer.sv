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
class producer #(type T=packet) extends uvm_component;

uvm_blocking_put_port #(T) put_port1;
uvm_blocking_put_port #(T) put_port;
uvm_blocking_get_port #(T) get_port;
uvm_blocking_transport_port #(T,T) trans_port;
uvm_blocking_peek_port #(T) peek_port;
uvm_nonblocking_put_port #(T) put_nb_port;
uvm_nonblocking_get_port #(T) get_nb_port;
uvm_nonblocking_peek_port #(T) peek_nb_port;
uvm_analysis_port #(T) a_port;

function new(string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV producer::new");
      put_port1 = new("put_port1",this);
      put_port = new("put_port",this);
      get_port = new("get_port",this);
      trans_port = new("trans_port",this);
      peek_port = new("peek_port",this);
      put_nb_port = new("put_nb_port",this);
      get_nb_port = new("get_nb_port",this);
      peek_nb_port = new("peek_nb_port",this);
      a_port = new("a_port",this);
endfunction

typedef producer#(T) prod_type;
`uvm_component_utils_begin(prod_type)
`uvm_component_utils_end
  
 
task run_phase(uvm_phase phase);
   T p;
   T q;
   int count;
   bit 	  b;  
   realtime ctime;
   
      phase.raise_objection(this);
      p = new;      
      q = new;      
      #50;
      put_port1.put(p); // start blocking from SC
      #50;
      for (count =0; count < 1; count++) begin	 
	 $display("[SV ",$realtime,,"*** Nonblocking transactions from SV ");
	 $display("[SV ",$realtime," ns] producer::can_put ");
	 ctime = $realtime;
	 b = put_nb_port.can_put();
	 $display("[SV ",$realtime," ns] producer::can_put returned ", b);
	 assert(b == 1);
	 assert(ctime==$realtime);
	 
	 #5;
	 p.next();
	 $display("[SV ",$realtime," ns] producer::putting ",p.data);
	 ctime = $realtime;
	 b = put_nb_port.try_put(p);
	 $display("[SV ",$realtime," ns] producer::put returned ");
	 assert(b == 1);
	 assert(ctime==$realtime);
	 
	 #5;
	 $display("[SV ",$realtime," ns] producer::can_get");
	 ctime = $realtime;
	 b = get_nb_port.can_get();
	 $display("[SV ",$realtime," ns] producer::can_get returned ", b);
	 assert(b == 1);
	 assert(ctime==$realtime);
	 
	 #5;
	 $display("[SV ",$realtime," ns] producer::get ");
	 ctime = $realtime;
	 b = get_nb_port.try_get(p);
	 $display("[SV ",$realtime," ns] producer::got ", p.data);
	 assert (b == 1);
	 assert(p.data==19);
	 assert(ctime==$realtime);
	 
	 #5;
	  $display("[SV ",$realtime," ns] producer::can_peek");
	 ctime = $realtime;
	 b = peek_nb_port.can_peek();
	 $display("[SV ",$realtime," ns] producer::can_peek returned ",b);
	 assert(b==1);
	 assert(ctime==$realtime);
	 
	 #5;
	 $display("[SV ",$realtime," ns] producer::peek ");
	 ctime = $realtime;
	 b = peek_nb_port.try_peek(p);
	 $display("[SV ",$realtime," ns] producer::got ", p.data);
	 assert(b==1);
	 assert(p.data==19);
	 assert(ctime==$realtime);
	 
	 #5;
	 $display("[SV ",$realtime," ns] producer::analysis ", p.data);
	 ctime = $realtime;
	 a_port.write(p);
	 assert(p.data==19);


	 
	 #5;
	 $display("[SV ",$realtime,,"*** Blocking transactions from SV ");
	 $display("[SV ",$realtime," ns] producer::get ");
	 ctime = $realtime;
	 get_port.get(p);
	 $display("[SV ",$realtime," ns] producer::got ", p.data);
	 assert(p.data==19);
	 assert($realtime==ctime+1);
	 
	 #4;
	 $display("[SV ",$realtime," ns] producer::transport ", p.data);
	 ctime = $realtime;
	 trans_port.transport(p,q);
	 $display("[SV ",$realtime," ns] producer::transport returned ", q.data);
	 assert(q.data==20);
	 assert($realtime==ctime+1);
	 
	 #4;
	 $display("[SV ",$realtime," ns] producer::peek ");
	 ctime = $realtime;
	 peek_port.peek(p);
	 $display("[SV ",$realtime," ns] producer::peek returned ", p.data);
	 assert(p.data==21);
	 assert($realtime==ctime);
	 
	 #4;
	 $display("[SV ",$realtime," ns] producer::putting ",p.data);
	 ctime = $realtime;
	 put_port.put(p);
	 $display("[SV ",$realtime," ns] producer::put returned ");
	 assert(p.data==21);
	 assert($realtime==ctime+1);
	 
	 #4;
      end
      phase.drop_objection(this);
      $display("** UVM TEST PASSED **");
endtask // run_phase


endclass

