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
  int init_delay;
  string target;

  function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV producer::new",UVM_LOW);
      b_put_port  = new("b_put_port",  this);
      nb_put_port = new("nb_put_port", this);
      b_initiator_socket  = new("b_initiator_socket", this);
      nb_initiator_socket = new("nb_initiator_socket", this);
  endfunction

  typedef producer#(T) prod_type2;
  `uvm_component_utils_begin(prod_type2)
  `uvm_component_utils_end
    
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV producer::build",UVM_LOW);
  endfunction

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
      bit [63:0] addr;
      
      delay = new(); 
      ph = BEGIN_REQ;
      for(int unsigned i = 0; i < init_delay; i++) begin
	 #1;
      end
            
      `uvm_info(get_type_name(),$sformatf("\n\n*** Starting non-blocking TLM2 transactions from SV to %s",target),UVM_LOW);
      addr = $urandom() & 'hff;
      trans = generate_transaction(addr, UVM_TLM_WRITE_COMMAND);
      trans.get_data(data);	 	 
      `uvm_info(get_type_name(),$sformatf("SV producer sends %d: %x %x %x %x ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
      sync = nb_initiator_socket.nb_transport_fw(trans, ph, delay);
      #5;
      
      trans = generate_transaction(addr, UVM_TLM_READ_COMMAND);
      trans.get_data(data);	 	 
      `uvm_info(get_type_name(),$sformatf("SV producer sends %d: %x %x %x %x ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
      sync = nb_initiator_socket.nb_transport_fw(trans, ph, delay);
      trans.get_data(data);	 	 
      `uvm_info(get_type_name(),$sformatf("SV producer received %d: %x %x %x %x ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
      #5;
            
      `uvm_info(get_type_name(),$sformatf("\n\n*** Starting blocking TLM2 transactions from SV to %s",target),UVM_LOW);
      addr = $urandom() & 'hff;
      trans = generate_transaction(addr, UVM_TLM_WRITE_COMMAND);
      trans.get_data(data);	 
      `uvm_info(get_type_name(),$sformatf("SV producer sends %d: %x %x %x %x ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
      b_initiator_socket.b_transport(trans, delay);

      trans = generate_transaction(addr, UVM_TLM_READ_COMMAND);
      trans.get_data(data);	 
      `uvm_info(get_type_name(),$sformatf("SV producer sends %d: %x %x %x %x ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);
      b_initiator_socket.b_transport(trans, delay);
      trans.get_data(data);	 	 
      `uvm_info(get_type_name(),$sformatf("SV producer received %d: %x %x %x %x ", trans.get_address(), data[0], data[1], data[2], data[3]),UVM_LOW);

      `uvm_info(get_type_name(),$sformatf("\n\n*** Starting non-blocking TLM1 transactions from SV to %s",target),UVM_LOW);
      for(int unsigned i = 1; i < 4; i++) begin
	 p = new();
	 p.data = i * 10;
	 `uvm_info(get_type_name(),$sformatf("SV producer sends %d", p.data),UVM_LOW);
	 res = nb_put_port.try_put(p);
	 #5;
      end

      #5;
      `uvm_info(get_type_name(),$sformatf("\n\n*** Starting blocking TLM1 transactions from SV to %s",target),UVM_LOW);
      for(int unsigned i = 1; i < 4; i++) begin
	 p = new();
	 p.data = i * 10;
	 `uvm_info(get_type_name(),$sformatf("SV producer sends %d", p.data),UVM_LOW);
	 b_put_port.put(p);	 
      end
  endtask: run_phase

  // generate generic payload for TLM2 transactions
  function uvm_tlm_generic_payload generate_transaction(bit [63:0] addr, uvm_tlm_command_e cmd);
      int unsigned length;
      byte unsigned data[];
      
      uvm_tlm_generic_payload t = new();
      length = 4;
      data = new[length];
      
      t.set_data_length(length);
      t.set_address(addr);
      
      for(int unsigned i = 0; i < length; i++) begin
	 if(cmd == UVM_TLM_WRITE_COMMAND)
	   data[i] = $urandom();
	 else
	   data[i] = 0;
      end
      
      t.set_data(data);
      t.set_byte_enable_length(0);
      t.set_response_status(UVM_TLM_INCOMPLETE_RESPONSE);
      t.set_command(cmd);
      
      return t;
  endfunction

endclass 

class producer_1 extends producer#(packet);

  function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV producer_1::new",UVM_LOW);
      init_delay = 0;
      target = "e";
  endfunction // new

  `uvm_component_utils(producer_1)

endclass
  
class producer_2 extends producer#(packet);

  function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info(get_type_name(),"SV producer_2::new",UVM_LOW);
      init_delay = 60;
      target = "SC";
  endfunction // new

  `uvm_component_utils(producer_2)

endclass 
