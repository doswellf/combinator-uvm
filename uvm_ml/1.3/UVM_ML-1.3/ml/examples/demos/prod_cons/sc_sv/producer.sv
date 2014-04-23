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

//uvm_blocking_put_port #(T) put_port1;
uvm_blocking_put_port #(T) put_port;
uvm_nonblocking_put_port #(T) put_nb_port;
uvm_tlm_nb_initiator_socket #(producer) nb_initiator_socket;
uvm_tlm_b_initiator_socket #() b_initiator_socket;
   int bw_count;
   
  function new(string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),"SV producer::new",UVM_LOW);
      put_port = new("put_port",this);
      put_nb_port = new("put_nb_port",this);
  endfunction

  typedef producer#(T) prod_type;
  `uvm_component_utils_begin(prod_type)
  `uvm_component_utils_end
  
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_type_name(),"SV producer::build",UVM_LOW);
      nb_initiator_socket = new("nb_initiator_socket", this);
      b_initiator_socket  = new("b_initiator_socket", this);
  endfunction

  function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info(get_type_name(),"SV producer::connect",UVM_LOW);
  endfunction

  // implement backword path for non-blocking TLM2 transaction
  function uvm_tlm_sync_e nb_transport_bw(uvm_tlm_generic_payload t,
                                      ref uvm_tlm_phase_e p,
                                      input uvm_tlm_time delay);
     uvm_report_warning("producer", "nb_transport_bw is not implemented");
     bw_count++;
     
  endfunction // nb_transport_bw
   

  // drive TLM1 and TLM2 transactions 
  task run_phase(uvm_phase phase);
      T p;
      int count;
      bit b;     
      uvm_tlm_time delay = new();
      uvm_tlm_phase_e ph;
      uvm_tlm_sync_e sync;
      uvm_tlm_generic_payload t;
     realtime ctime;
     
      phase.raise_objection(this);
      ph = BEGIN_REQ;
      p = new;      
      #110;
      
      // start TLM1 transactions
      `uvm_info(get_type_name(),"\nNonblocking TLM1 transactions from SV ",UVM_LOW);
      for (count =0; count < 3; count++) begin	 
	 `uvm_info(get_type_name(),"SV producer::can_put ",UVM_LOW);
	 ctime = $realtime;
	 b = put_nb_port.can_put();
	 assert($realtime==ctime);
	 `uvm_info(get_type_name(),$sformatf("SV producer::can_put returned %d", b),UVM_LOW);
	 #5;
	 p.next();

	 `uvm_info(get_type_name(),$sformatf("SV producer::try_put %d",p.data),UVM_LOW);
	 b = put_nb_port.try_put(p);
	 `uvm_info(get_type_name(),"SV producer::try_put returned ",UVM_LOW);
      end // for
      #35;
      
      `uvm_info(get_type_name(),"\nBlocking TLM1 transactions from SV ",UVM_LOW);
      for (count =0; count < 3; count++) begin	 
	 `uvm_info(get_type_name(),$sformatf("SV producer::putting %d",p.data),UVM_LOW);
	 put_port.put(p);
	 p.next();
	 `uvm_info(get_type_name(),"SV producer::put returned ",UVM_LOW);
	 #4;
      end // for
      
      // start TLM2 transactions
      `uvm_info(get_type_name(),"\nTLM2 non-blocking transactions from SV ",UVM_LOW);
      #35
      for(count = 0; count < 3; count++) begin
         t = generate_transaction();
	 `uvm_info(get_type_name(),$sformatf("SV producer %s", t.convert2string()),UVM_LOW);
	 ctime = $realtime;
         sync = nb_initiator_socket.nb_transport_fw(t, ph, delay);
	  assert($realtime==ctime);
	 #5;
      end
      
      `uvm_info(get_type_name(),"\nTLM2 blocking transactions from SV ",UVM_LOW);
      #35
      for(count = 3; count < 6; count++) begin
         t = generate_transaction();
	 `uvm_info(get_type_name(),$sformatf("SV producer %s", t.convert2string()),UVM_LOW);
	 ctime = $realtime;
         b_initiator_socket.b_transport(t, delay);
	 assert($realtime==ctime+10);
      end
     assert(bw_count==0);
     
      phase.drop_objection(this);
  endtask // run_phase

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

