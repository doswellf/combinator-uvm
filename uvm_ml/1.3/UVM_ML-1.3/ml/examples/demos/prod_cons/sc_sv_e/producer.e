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
    // SV interface
    nb_socket  : tlm_initiator_socket of tlm_generic_payload is instance;
    b_socket   : tlm_initiator_socket of tlm_generic_payload is instance;
    sv_put_port   : out interface_port of tlm_blocking_put of packet is instance;
       keep bind(sv_put_port,external);
    sv_nb_put_port: out interface_port of tlm_nonblocking_put of packet is instance;
       keep bind(sv_nb_put_port,external);
    // SC interface
    sc_socket  : tlm_initiator_socket of tlm_generic_payload is instance;
    put_port   : out interface_port of tlm_blocking_put of packet is instance;
       keep bind(put_port,external);
    nb_put_port: out interface_port of tlm_nonblocking_put of packet is instance;
       keep bind(nb_put_port,external);
    
    gp1   : tlm_generic_payload;
    gp2   : tlm_generic_payload;
    status: tlm_sync_enum;

    connect_ports() is also {
        nb_socket.connect(external);
        b_socket.connect(external);
        sc_socket.connect(external);
    };
    
    run() is also {
        start drive();
    };
    
    drive()@sys.any is {
       var ind: uint = 1;
       wait delay (130);
       
       out("\n\n*** Starting non-blocking TLM2 transactions from e to SV");
       gp1 = create_trans(ind, TLM_WRITE_COMMAND);
       message(LOW,append("Calling nb_transport_fw with data size ",gp1.m_length));
       var phase : tlm_phase_enum = BEGIN_REQ;
       var t: time = 0;
       status = nb_socket$.nb_transport_fw(gp1, phase, t);
       check that status == TLM_COMPLETED;
       wait delay (10);
        
       gp2 = create_trans(ind, TLM_READ_COMMAND);
       message(LOW,append("Calling nb_transport_fw with data size ",gp2.m_length));
       status = nb_socket$.nb_transport_fw(gp2, phase, t);
       message(LOW,append("Received data ",hex(gp2.m_data)));
       check that status == TLM_COMPLETED;
       check that gp1.m_data == gp2.m_data;
       wait delay (10);
       ind = ind + 2;
       
       
       
       out("\n\n*** Starting blocking TLM2 transactions from e to SV");
       var before := sys.time;
       gp1 = create_trans(ind, TLM_WRITE_COMMAND);
       message(LOW,append("Calling b_transport with data size ",gp1.m_length));
       t = 10;
       b_socket$.b_transport(gp1, t);
       check that before+10 == sys.time;
       before+=10;
       
       gp2 = create_trans(ind, TLM_READ_COMMAND);
       message(LOW,append("Calling b_transport with data size ",gp2.m_length));
       b_socket$.b_transport(gp2, t);
       message(LOW,append("Received data ", hex(gp2.m_data)));
       check that before+10 == sys.time;
       check that gp1.m_data == gp2.m_data;
       ind = ind + 2;
        
       
       
       wait delay(10);
       out("\n\n*** Starting non-blocking TLM1 transactions from e to SV");
       for i from 1 to 3 {
          var p : packet;
          gen p keeping {.data == 17+i};
          message(LOW, "Sending  packet = ", p);
          var res := sv_nb_put_port$.try_put(p);
          wait delay(10);
       };
       
       
       
       out("\n\n*** Starting blocking TLM1 transactions from e to SV");
       before = sys.time;
       for i from 4 to 6 {
          var p : packet;
          gen p keeping {.data == 17+i};
          message(LOW, "Sending  packet = ", p);
          sv_put_port$.put(p);
          wait delay(9);
           check that before+10 == sys.time;
          before+=10;
       };
       
       
       
       out("\n\n*** Starting blocking TLM1 transactions from e to SC");
       for i from 7 to 9 {
          var p : packet;
          gen p keeping {.data == 17+i};
          message(LOW,append("Calling put with data ",p.data));
          put_port$.put(p);
       };
       wait delay(5);
       
       
       
       out("\n\n*** Starting non-blocking TLM1 transactions from e to SC");
       for i from 10 to 12 {
          var p : packet;
          gen p keeping {.data == 17+i};
          message(LOW,append("Calling nb_put with data ",p.data));
          var res := nb_put_port$.try_put(p);
          wait delay (5);
       };
       wait delay(5);       
       
       
       out("\n\n*** Starting blocking TLM2 transactions from e to SC");
       before = sys.time;
       t = 5;
       gp1 = create_trans(ind, TLM_WRITE_COMMAND);
       message(LOW,append("Calling b_transport WRITE with data ",hex(gp1.m_data)));
       sc_socket$.b_transport(gp1, t);
       check that before+5 == sys.time;
       before+=5;
       
       gp2 = create_trans(ind, TLM_READ_COMMAND);
       message(LOW,append("Calling b_transport READ with data ",hex(gp2.m_data)));
       sc_socket$.b_transport(gp2, t);
       message(LOW,append("b_transport received ",hex(gp2.m_data)));
       check that before+5 == sys.time;
       check that gp1.m_data == gp2.m_data;
       ind += 2;
       
       
       
       out("\n\n*** Starting non-blocking TLM2 transactions from e to SC");
       gp1 = create_trans(ind, TLM_WRITE_COMMAND);
       message(LOW,append("Calling nb_transport WRITE with data ",hex(gp1.m_data)));
       status = sc_socket$.nb_transport_fw(gp1, phase, t);
       wait delay (5);
       
       gp2 = create_trans(ind, TLM_READ_COMMAND);
       message(LOW,append("Calling nb_transport READ with data ",hex(gp2.m_data)));
       status = sc_socket$.nb_transport_fw(gp2, phase, t);
       message(LOW,append("nb_transport received ",hex(gp2.m_data)));
       check that gp1.m_data == gp2.m_data;
       wait delay (5);
       ind += 2;
    };
    
    // Create generic payload
    create_trans(base:uint, cmd: tlm_command) : tlm_generic_payload is { 
       gen result keeping {
          .m_address == base*1024;
          .m_command == cmd;
          .m_length == 4;
          .m_data.size() == .m_length;
          .m_response_status == TLM_INCOMPLETE_RESPONSE;
          .m_byte_enable_length == 0;
          .m_byte_enable.size() == .m_byte_enable_length;
          .m_extensions.size() == 0;
       }; // gen result keep...
    };
    
    nb_transport_bw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
        message(LOW,"Received nb_transport_bw ", trans.m_response_status);
        return TLM_COMPLETED;
    };
    
};
'>