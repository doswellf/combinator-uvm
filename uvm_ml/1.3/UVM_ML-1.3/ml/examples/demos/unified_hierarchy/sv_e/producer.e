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
    b_socket  : tlm_initiator_socket of tlm_generic_payload is instance;
    nb_socket : tlm_initiator_socket of tlm_generic_payload is instance;
    address   : int;
       keep uvm_config_get(address);

    run() is also {
       start drive();
    };
    
    drive()@sys.any is {
       //var addr: uint = 100;
       var phase: tlm_phase_enum;
       var t: time;
       var gp: tlm_generic_payload;
       var status: tlm_sync_enum;

       wait delay (10);
       
       out("\n\n*** Starting non-blocking TLM2 transactions from e");
       gp = create_trans(address, TLM_WRITE_COMMAND);
       message(LOW,append("Calling nb_transport_fw WRITE ",hex(gp.m_data)));
       phase = BEGIN_REQ;
       t = 5;
       status = nb_socket$.nb_transport_fw(gp, phase, t);
       wait delay (10);
       
       gp = create_trans(address, TLM_READ_COMMAND);
       message(LOW,append("Calling nb_transport_fw READ ",hex(gp.m_data)));
       phase = BEGIN_REQ;
       t = 5;
       status = nb_socket$.nb_transport_fw(gp, phase, t);
       message(LOW,append("nb_transport READ returned ",hex(gp.m_data)));
       wait delay (10);
      
       out("\n\n*** Starting blocking TLM2 transactions from e");
       gp = create_trans(address, TLM_WRITE_COMMAND);
       message(LOW,append("Calling b_transport WRITE ",hex(gp.m_data)));
       t = 5;
       b_socket$.b_transport(gp, t);
       wait delay (5);
       
       gp = create_trans(address, TLM_READ_COMMAND);
       message(LOW,append("Calling b_transport READ ",hex(gp.m_data)));
       t = 5;
       b_socket$.b_transport(gp, t);
       message(LOW,append("b_transport READ returned ",hex(gp.m_data)));
    };
    
    // Create generic payload with random data of length 4
    create_trans(addr:uint, cmd: tlm_command) : tlm_generic_payload is {       
        result = new;
        
        result.m_address = addr;
        result.m_command = cmd;
        if(cmd == TLM_READ_COMMAND) {
           for i from 0 to 3 do {
              result.m_data.add(0);
           }; 
        } else {
           gen result.m_data keeping {.size() == 4};
        };
        result.m_length = result.m_data.size();
        result.m_response_status = TLM_INCOMPLETE_RESPONSE;
        result.m_byte_enable_length = 0;
    };
    
    nb_transport_bw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
        message(LOW,"Received nb_transport_bw ", trans.m_response_status, " phase= ", phase);
        return TLM_COMPLETED;
    };
    
};
'>