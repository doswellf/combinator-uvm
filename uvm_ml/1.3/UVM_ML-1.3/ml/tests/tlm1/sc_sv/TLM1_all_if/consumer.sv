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
  class consumer #(type T=packet) extends uvm_component;
    uvm_blocking_put_imp #(T, consumer #(T)) put_export;
    uvm_blocking_get_imp #(T, consumer #(T)) get_export;
    uvm_blocking_peek_imp #(T, consumer #(T)) peek_export;
    uvm_blocking_transport_imp #(T, T, consumer #(T)) trans_export;
    uvm_nonblocking_put_imp #(T, consumer #(T)) put_nb_export;
    uvm_nonblocking_get_imp #(T, consumer #(T)) get_nb_export;
    uvm_nonblocking_peek_imp #(T, consumer #(T)) peek_nb_export;
    uvm_analysis_imp #(T, consumer#(T)) a_export;
     int save;
     int check_sum;
     
  
    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      $display("SV consumer::new");
      put_export = new("put_export",this);
      get_export = new("get_export",this);
      peek_export = new("peek_export",this);
      trans_export = new("trans_export",this);
      put_nb_export = new("put_nb_export",this);
      get_nb_export = new("get_nb_export",this);
      peek_nb_export = new("peek_nb_export",this);
      a_export = new("a_export",this);
       check_sum = 0;
    endfunction
  
    typedef consumer#(T) cons_type;
    `uvm_component_utils_begin(cons_type)
    `uvm_component_utils_end
  
    task put (T p);
      $display("[SV ",$realtime," ns] consumer::put",p.data);
      save = p.data;
       assert(save == 17);
       check_sum = check_sum + 1;
      #1;
      $display("[SV ",$realtime," ns] consumer::put returns", p.data);
    endtask 
  

    task get(output T p);
      T tmp = new();
      tmp.data = save+1;
      p = tmp;
      $display("[SV ",$realtime," ns] consumer::get",p.data);
      #1;
      $display("[SV ",$realtime," ns] consumer::get returns", p.data);
       check_sum = check_sum + 1;
    endtask

    task transport(input T req, output T rsp);
      rsp = new;
      //static T t1 = new();
      $display("[SV ",$realtime," ns] consumer::transport", req.data);
       assert(req.data == 19);
      rsp.data = req.data+1;
      #1;
      //rsp = t1; 
      $display("[SV ",$realtime," ns] consumer::transport returns", rsp.data);
       check_sum = check_sum + 1;
    endtask

    task peek (output T t);
      T t1 = new();
      t1.data = save+1;
      #1;
      $display("[SV ",$realtime," ns] consumer::peek(), returns", t1.data);
      t = t1;
       check_sum = check_sum + 1;
    endtask
 
    function bit try_put (T p);
       static int idx = 0;
      $display("[SV ",$realtime," ns] consumer::try_put ",p.data);
      save = p.data;
       assert(save == 17 + idx);
       idx++;
       check_sum = check_sum + 1;
      return 1;
    endfunction 
  
    function bit can_put ();
      $display("[SV ",$realtime," ns] consumer::can_put()");
       check_sum = check_sum + 1;
      return 1;
    endfunction 
 
    function bit try_get (output T p);
      T tmp = new();
      tmp.data = save+1;
      p = tmp;
      $display("[SV ",$realtime," ns] consumer::try_get ",p.data);
       check_sum = check_sum + 1;
      return 1;
    endfunction 
  
    function bit can_get ();
      $display("[SV ",$realtime," ns] consumer::can_get()");
       check_sum = check_sum + 1;
      return 1;
    endfunction 
 
    function bit try_peek(output T t);
      static T t1 = new();
      t1.next();
      $display("[SV ",$realtime," ns] consumer::try_peek(), sending ", t1.data);
      t = t1;
       check_sum = check_sum + 1;
      return 1;
    endfunction // bit

    function bit can_peek();
      $display("[SV ",$realtime," ns] consumer::can_peek, returning 0");
       check_sum = check_sum + 1;
      return 1;
    endfunction 

    function void write(input T t); 
      $display("[SV ",$realtime," ns] consumer::write received ", t.data);
       check_sum = check_sum + 1;
       assert(t.data == 18);
    endfunction

  endclass
