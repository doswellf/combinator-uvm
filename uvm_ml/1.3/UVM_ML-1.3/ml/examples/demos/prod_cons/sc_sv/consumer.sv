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
  uvm_nonblocking_put_imp #(T, consumer #(T)) put_nb_export;
  uvm_tlm_nb_target_socket #(consumer) nb_target_socket;
  uvm_tlm_b_target_socket #(consumer) b_target_socket;
  int unsigned transaction_count;
  int save;
  byte unsigned save_gp[];
  int save_length;
      
  
  typedef consumer#(T) cons_type;
  `uvm_component_utils_begin(cons_type)
  `uvm_component_utils_end
  
  function new(string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),"SV consumer::new",UVM_LOW);
      put_export = new("put_export",this);
      put_nb_export = new("put_nb_export",this);
  endfunction
  
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV consumer::build",UVM_LOW);
      nb_target_socket = new("nb_target_socket", this, this);
      b_target_socket  = new("b_target_socket", this, this);
  endfunction

  function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),"SV consumer::connect",UVM_LOW);
  endfunction

  // implement non-blocking TLM2 socket
  function uvm_tlm_sync_e nb_transport_fw(uvm_tlm_generic_payload t,
                                          ref uvm_tlm_phase_e p,
					  input uvm_tlm_time delay);
      uvm_tlm_sync_e res;
      `uvm_info(get_type_name(),$sformatf("SV nb_transport_fw %s", t.convert2string()),UVM_LOW);
      transaction_count++;
      if(t.is_write) begin
	 t.get_data(save_gp);
	 save_length = t.get_data_length();
      end
      if(t.is_read) begin
	 t.set_data_length(save_length);
	 t.set_data(save_gp);
      end
      p = BEGIN_RESP;
      res = nb_target_socket.nb_transport_bw(t,p,delay);    
      return UVM_TLM_COMPLETED;
  endfunction

  // implement blocking TLM2 socket
  task b_transport(uvm_tlm_generic_payload t,
		   input uvm_tlm_time delay);
      `uvm_info(get_type_name(),$sformatf("SV b_transport %s", t.convert2string()),UVM_LOW);
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
      #10;
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
      `uvm_info(get_type_name(),$sformatf("SV consumer::can_put()"),UVM_LOW);
      transaction_count++;
      return 1;
  endfunction // can_put

  // check all transactions were received
  function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      if(transaction_count == 13)
        `uvm_info(get_type_name(),"** UVM TEST PASSED **",UVM_LOW)
      else
        `uvm_info(get_type_name(),$sformatf("** UVM TEST FAILED ** transaction count= %d", transaction_count),UVM_LOW) 
  endfunction

endclass
