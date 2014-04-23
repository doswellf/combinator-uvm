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

<'
unit producer like uvm_bfm {
    nb_socket : tlm_initiator_socket of tlm_generic_payload is instance;
    b_socket  : tlm_initiator_socket of tlm_generic_payload is instance;
    get_port  : out interface_port of tlm_get of packet is instance;
       keep bind(get_port,external);
    
    connect_ports() is also {
        nb_socket.connect(external);
        b_socket.connect(external);
    };
    
    run() is also {
        start drive();
    };
    
    !completed_counter : uint;    
    drive()@sys.any is {
       var ind: uint = 0;
       wait delay (100);
       out("\n\n*** Starting non-blocking TLM2 transactions from e");
       while (ind < 3) {
          var gp := create_trans(ind, TLM_WRITE_COMMAND);
          message(LOW,append("Calling nb_transport_fw with data size ",gp.m_length));
          var phase : tlm_phase_enum = BEGIN_REQ;
          var t: time = 0;
          var status := nb_socket$.nb_transport_fw(gp, phase, t);
          check that status == TLM_COMPLETED;
          wait delay (50);
          ind += 1;
       };
       
       out("\n\n*** Starting blocking TLM2 transactions from e");
       var before := sys.time;
       while (ind < 6) {
          var gp := create_trans(ind, TLM_WRITE_COMMAND);
          message(LOW,append("Calling b_transport with data size ",gp.m_length));
          var phase : tlm_phase_enum = BEGIN_REQ;
          var t: time = 50;
          b_socket$.b_transport(gp, t);
          check that before+50 == sys.time;
          before+=50;
          ind += 1;
       };
       
       out("\n\n*** Starting non-blocking TLM1 transactions from e");
       for i from 1 to 3 {
          var p : packet;
          var res : bool;
          res = get_port$.try_get(p);
          
          message(LOW, "Got res = ", res, ", packet = ", p);
          check that res;           
          check that p.data == i * 10;
          check that p.trailer == i * 20;
          check that p.txt == appendf("Iteration # %d",i);
          completed_counter+=1;
          wait delay(50);
       };
       
       out("\n\n*** Starting blocking TLM1 transactions from e");
       before = sys.time;
       for i from 4 to 6 {
          var p : packet;
          get_port$.get(p);
          message(LOW, "Got packet = ", p);
          check that p.data == i*10;
          check that p.trailer == i*20;
          check that p.txt == appendf("Iteration # %0d",i);
          check that before+50 == sys.time;
          before+=50;
          completed_counter+=1;
       };
    };
    
    // Create generic payload
    create_trans(base:uint, cmd: tlm_command) : tlm_generic_payload is {       
        result = new;
        
        result.m_address = base*1024;
        result.m_command = cmd;
        for i from 0 to base do {
             result.m_data.add(i);
        };
        result.m_length = result.m_data.size();
        result.m_response_status = TLM_INCOMPLETE_RESPONSE;
        result.m_byte_enable_length = 0;
    };
    
    nb_transport_bw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
        message(LOW,"Received nb_transport_bw ", trans.m_response_status);
        return TLM_COMPLETED;
    };
    
};
'>