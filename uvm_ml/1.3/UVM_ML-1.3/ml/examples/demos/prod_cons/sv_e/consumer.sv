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

//----------------------------------------------------------------------
// consumer
// Respond to messages from e producer
//----------------------------------------------------------------------
class consumer #(type T=packet) extends uvm_component;

    uvm_tlm_nb_target_socket #(consumer) nb_target_socket;
    uvm_tlm_b_target_socket  #(consumer) b_target_socket;
    uvm_get_imp #(T, consumer) get_imp;

    int unsigned transaction_count;
    int call_index;

    typedef consumer#(T) cons_type;
    `uvm_component_utils_begin(cons_type)
    `uvm_component_utils_end
 
    function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV consumer::new",UVM_LOW);
      get_imp = new("get_imp", this);
      call_index = 1;      
    endfunction


    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV consumer::build",UVM_LOW);
      nb_target_socket = new("nb_target_socket", this, this);
      b_target_socket  = new("b_target_socket", this,this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),"SV consumer::connect",UVM_LOW);
    endfunction

    //TLM2 functions implementation
    function uvm_tlm_sync_e nb_transport_fw(uvm_tlm_generic_payload t,
                                            ref uvm_tlm_phase_e p,
					    input uvm_tlm_time delay);
        uvm_tlm_sync_e res;
        t.set_response_status(UVM_TLM_OK_RESPONSE);
	`uvm_info(get_type_name(),$sformatf("SV consumer received %s", t.convert2string()),UVM_LOW);
        transaction_count++;
        return UVM_TLM_COMPLETED;
    endfunction

    task b_transport(uvm_tlm_generic_payload t, uvm_tlm_time delay);
        for (integer i = 0; i < delay.get_realtime(1ns); i++) begin
	   #1;
	end
        t.set_response_status(UVM_TLM_OK_RESPONSE);
	`uvm_info(get_type_name(),$sformatf("SV consumer received %s", t.convert2string()),UVM_LOW);
        transaction_count++;
    endtask

   //get functions implementation
   virtual task get(output T obj);
      string exp_txt;
      obj = new;   
      obj.data = call_index * 10;
      obj.trailer = call_index * 20;
      obj.txt = $psprintf("Iteration # %0d",call_index);
      `uvm_info(get_type_name(),$sformatf("SV consumer get data = %0d trailer = %0d  txt = %s", obj.data, obj.trailer, obj.txt),UVM_LOW);
      call_index++;
      #50;
      transaction_count++;
   endtask // get

   virtual function bit try_get(output T obj);
      string exp_txt;
      obj = new;   
      obj.data = call_index * 10;
      obj.trailer = call_index * 20;
      obj.txt = $psprintf("Iteration # %0d",call_index);
      `uvm_info(get_type_name(),$sformatf("SV consumer get data = %0d trailer = %0d  txt = %s", obj.data, obj.trailer, obj.txt),UVM_LOW);
      call_index++;
      try_get = 1;
      transaction_count++;
   endfunction // try_get
   
   virtual function bit can_get();
      `uvm_info(get_type_name(),$sformatf("going to return %d",can_get),UVM_LOW);
   endfunction 

   function void report();
      if(transaction_count == 12)
        `uvm_info(get_type_name(),"** UVM TEST PASSED **",UVM_LOW)
      else
        `uvm_info(get_type_name(),$sformatf("** UVM TEST FAILED ** transaction count=%0d", transaction_count),UVM_LOW) 
   endfunction

endclass
