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
// Respond to messages from ML producer
//----------------------------------------------------------------------
  
class consumer #(type T=packet) extends uvm_component;

    uvm_tlm_nb_target_socket #(consumer) nb_target_socket;
    uvm_tlm_b_target_socket  #(consumer) b_target_socket;
    uvm_blocking_put_imp #(T, consumer #(T)) put_export;
    uvm_nonblocking_put_imp #(T, consumer #(T)) put_nb_export;

    int unsigned transaction_count;
    int call_index;
    int save;
    byte unsigned save_gp[];
    int save_length;

    typedef consumer#(T) cons_type2;
    `uvm_component_utils_begin(cons_type2)
    `uvm_component_utils_end
 
    function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV consumer::new",UVM_LOW);
      put_export = new("put_export",this);
      put_nb_export = new("put_nb_export",this);
      call_index = 1;      
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV consumer::build",UVM_LOW);
      nb_target_socket = new("nb_target_socket", this, this);
      b_target_socket  = new("b_target_socket",  this, this);
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
      if(t.is_write) begin
	 t.get_data(save_gp);
	 save_length = t.get_data_length();
      end
      if(t.is_read) begin
	 t.set_data_length(save_length);
	 t.set_data(save_gp);
      end
      t.set_response_status(UVM_TLM_OK_RESPONSE);
      return UVM_TLM_COMPLETED;
    endfunction

    task b_transport(uvm_tlm_generic_payload t, uvm_tlm_time delay);
      for (integer i = 0; i < delay.get_realtime(1ns); i++) begin
	 #1;
      end
      t.set_response_status(UVM_TLM_OK_RESPONSE);
      `uvm_info(get_type_name(),$sformatf("SV consumer received %s", t.convert2string()),UVM_LOW);
      transaction_count++;
      if(t.is_write) begin
	 t.get_data(save_gp);
	 save_length = t.get_data_length();
      end
      if(t.is_read) begin
	 t.set_data_length(save_length);
	 t.set_data(save_gp);
      end     
    endtask

  // implement TLM1 put interface
  task put (T p);
      `uvm_info(get_type_name(),$sformatf("SV consumer::put %d",p.data),UVM_LOW);
      transaction_count++;
      save = p.data;
      #1;
      `uvm_info(get_type_name(),$sformatf("SV consumer::put returns %d", p.data),UVM_LOW);
  endtask 
  
  function bit try_put (T p);
      `uvm_info(get_type_name(),$sformatf("SV consumer::try_put %d",p.data),UVM_LOW);
      transaction_count++;
      save = p.data;
      return 1;
  endfunction 
  
  function bit can_put ();
      `uvm_info(get_type_name(),"SV consumer::can_put()",UVM_LOW);
      transaction_count++;
      return 1;
  endfunction 

endclass
  
class consumer_1 extends consumer#(packet);

  function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV consumer_1::new",UVM_LOW);
  endfunction // new
  `uvm_component_utils(consumer_1)

  function void report();
      if(transaction_count == 10)
        `uvm_info(get_type_name(),"** UVM TEST PASSED **",UVM_LOW)
      else
        `uvm_info(get_type_name(),$sformatf("** UVM TEST FAILED ** transaction count= %d", transaction_count),UVM_LOW)
  endfunction

endclass
  
class consumer_2 extends consumer#(packet);

  function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV consumer_2::new",UVM_LOW);
  endfunction // new

  `uvm_component_utils(consumer_2)
endclass
