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
// producer
// Send messages to ML consumer
//----------------------------------------------------------------------
class producer #(type T=packet) extends uvm_component;

  uvm_tlm_b_initiator_socket #() b_initiator_socket;
  uvm_tlm_nb_initiator_socket #(producer) nb_initiator_socket;
  uvm_blocking_put_port #(T) b_put_port;
  uvm_nonblocking_put_port #(T) nb_put_port;

  function new(string name, uvm_component parent);
      super.new(name, parent);
      b_put_port  = new("b_put_port", this);
      nb_put_port = new("nb_put_port", this);
      `uvm_info(get_type_name(),"SV producer::new",UVM_LOW);
  endfunction

  typedef producer#(T) prod_type;
  `uvm_component_utils_begin(prod_type)
  `uvm_component_utils_end
    
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV producer::build",UVM_LOW);
      b_initiator_socket  = new("b_initiator_socket", this);
      nb_initiator_socket = new("nb_initiator_socket", this);
  endfunction

  // register the initiator socket
  function void phase_ended(uvm_phase phase);
      if (phase.get_name() == "build") begin
	 //uvm_ml::ml_tlm2#()::register(b_initiator_socket);
	 //uvm_ml::ml_tlm2#()::register(nb_initiator_socket);
      end
  endfunction // void

  function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),"SV producer::connect",UVM_LOW);
  endfunction

  function uvm_tlm_sync_e nb_transport_bw(uvm_tlm_generic_payload t,
					  ref uvm_tlm_phase_e p,
					  input uvm_tlm_time delay);
      uvm_report_warning("producer", "nb_transport_bw is not implemented");
  endfunction

  // drive TLM1 and TLM2 transactions 
  task run_phase (uvm_phase phase);
      uvm_tlm_generic_payload trans;
      uvm_tlm_time delay;
      uvm_tlm_phase_e ph;
      uvm_tlm_sync_e sync;
      T p;
      bit res;
      byte unsigned data[4];
      
      delay = new(); 
      ph = BEGIN_REQ;

      `uvm_info(get_type_name(),"\n\n*** Starting non-blocking TLM2 transactions from SV",UVM_LOW);
      for(int unsigned i = 1; i < 4; i++) begin
	 trans = generate_transaction();
	 trans.get_data(data);	 
	 `uvm_info(get_type_name(),$sformatf("SV producer sends %d: %d %d %d %d ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
	 sync = nb_initiator_socket.nb_transport_fw(trans, ph, delay);
	 #5;
      end
      
      `uvm_info(get_type_name(),"\n\n*** Starting blocking TLM2 transactions from SV",UVM_LOW);
      for(int unsigned i = 1; i < 4; i++) begin
	 trans = generate_transaction();
	 trans.get_data(data);	 
	 `uvm_info(get_type_name(),$sformatf("SV producer sends %d: %d %d %d %d ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
	 b_initiator_socket.b_transport(trans, delay);
      end
      
      `uvm_info(get_type_name(),"\n\n*** Starting non-blocking TLM1 transactions from SV",UVM_LOW);
      for(int unsigned i = 1; i < 4; i++) begin
	 p = new();
	 p.data = i * 10;
	 p.trailer = i * 20;
	 p.txt = $psprintf("Iteration # %0d",i);
	 `uvm_info(get_type_name(),$sformatf("SV producer sends %d %d %s", p.data, p.trailer, p.txt),UVM_LOW);
	 res = nb_put_port.try_put(p);
	 #5;
      end

      `uvm_info(get_type_name(),"\n\n*** Starting blocking TLM1 transactions from SV",UVM_LOW);
      for(int unsigned i = 1; i < 4; i++) begin
	 p = new();
	 p.data = i * 10;
	 p.trailer = i * 20;
	 p.txt = $psprintf("Iteration # %0d",i);
	 `uvm_info(get_type_name(),$sformatf("SV producer sends %d %d %s", p.data, p.trailer, p.txt),UVM_LOW);
	 b_put_port.put(p);	 
      end
      
  endtask: run_phase

  // generate generic payload for TLM2 transactions
  function uvm_tlm_generic_payload generate_transaction();
      bit [63:0] addr;
      int unsigned length;
      byte unsigned data[];
      
      uvm_tlm_generic_payload t = new();
      addr = $urandom() & 'hff;
      length = 4;
      data = new[length];
      
      t.set_data_length(length);
      t.set_address(addr);
      
      for(int unsigned i = 0; i < length; i++) begin
	 data[i] = $urandom();
      end
      
      t.set_data(data);
      t.set_byte_enable_length(0);
      t.set_response_status(UVM_TLM_INCOMPLETE_RESPONSE);
      t.set_command(UVM_TLM_WRITE_COMMAND);
      
      return t;
  endfunction

endclass