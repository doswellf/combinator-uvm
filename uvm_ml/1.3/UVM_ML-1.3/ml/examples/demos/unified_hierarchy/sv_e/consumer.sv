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

// Consumer class responds to TLM2 transactions
class consumer extends uvm_component;
    uvm_tlm_b_target_socket #(consumer) b_target_socket;
    uvm_tlm_nb_target_socket #(consumer) nb_target_socket;
    // Save data for read after write; address being ignored
    byte unsigned save_gp[];
    int save_length;
    // Queue non-blocking transactions
    uvm_tlm_generic_payload itemQ[$];
    uvm_tlm_time delayQ[$];
  
    typedef consumer cons_type;
    `uvm_component_utils_begin(cons_type)
    `uvm_component_utils_end
  
    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),"SV consumer::new",UVM_LOW);
    endfunction
  
    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV consumer::build",UVM_LOW);
      b_target_socket  = new("b_target_socket", this, this);
      nb_target_socket = new("nb_target_socket", this, this);
    endfunction

    // Delayed response to non-blocking calls
    task run_phase(uvm_phase phase);
      uvm_tlm_generic_payload t;
      uvm_tlm_sync_e res;
      uvm_tlm_phase_e ph;
      uvm_tlm_time delay;
      
      while (1) begin
	 wait(itemQ.size() > 0);
	 delay = delayQ.pop_front();
	 t = itemQ.pop_front();
	 #(delay.get_realtime(1ns));
	 delay.reset();
	 
	 ph = BEGIN_RESP;
         `uvm_info(get_type_name(),$sformatf("SV consumer responds %s", t.convert2string()),UVM_LOW);
	 res = nb_target_socket.nb_transport_bw(t, ph, delay);    
      end;
    endtask // run_phase

  
    // implement non-blocking TLM2 socket
    function uvm_tlm_sync_e nb_transport_fw(uvm_tlm_generic_payload t,
                                            ref uvm_tlm_phase_e p,
					    input uvm_tlm_time delay);
      `uvm_info(get_type_name(),$sformatf("SV consumer::nb_transport_fw %s", t.convert2string()),UVM_LOW);
      if(t.is_write) begin
	 t.get_data(save_gp);
	 save_length = t.get_data_length();
      end
      if(t.is_read) begin
	 t.set_data_length(save_length);
	 t.set_data(save_gp);
      end
      itemQ.push_back(t);
      delayQ.push_back(delay);
      t.set_response_status(UVM_TLM_OK_RESPONSE);
      return UVM_TLM_ACCEPTED;
    endfunction

    // implement blocking TLM2 socket
    task b_transport(uvm_tlm_generic_payload t,
		     uvm_tlm_time delay);
      
      `uvm_info(get_type_name(),$sformatf("SV consumer::b_transport %s", t.convert2string()),UVM_LOW);
      #(delay.get_realtime(1ns));
      delay.reset();
     
      if(t.is_write) begin
	 t.get_data(save_gp);
	 save_length = t.get_data_length();
      end
      if(t.is_read) begin
	 t.set_data_length(save_length);
	 t.set_data(save_gp);
      end
      
      t.set_response_status(UVM_TLM_OK_RESPONSE);
      `uvm_info(get_type_name(),$sformatf("SV consumer::b_transport responds %s", t.convert2string()),UVM_LOW);
    endtask

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV consumer::connect %s", get_full_name()),UVM_LOW);
    endfunction

    function void resolve_bindings();
      `uvm_info(get_type_name(),$sformatf("SV consumer::resolve_bindings %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void end_of_elaboration();
      `uvm_info(get_type_name(),$sformatf("SV consumer::end_of_elaboration %s", get_full_name()),UVM_LOW);
    endfunction
   
    function void start_of_simulation();
      `uvm_info(get_type_name(),$sformatf("SV consumer::start_of_simulation %s", get_full_name()),UVM_LOW);
    endfunction
   
   
endclass

    