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
uvm_ml_type_match "e:tlm::tlm_generic_payload" "sv:uvm_pkg::uvm_tlm_generic_payload";

unit producer {
  
    isocket : tlm_initiator_socket of tlm_generic_payload is instance;
    
    connect_ports() is also {
        isocket.connect(external);
    };
    
    run() is also {
        start ver();
    };
    
    ver()@sys.any is {
        var ind: uint = 0;
        message(LOW,"Starting ver()");
        while (ind < 10) {
            var gp := create_trans(ind,TLM_WRITE_COMMAND);
            wait delay (50);
            message(LOW,append("Calling nb_transport_fw with data size ",gp.m_length));
            var phase : tlm_phase_enum = BEGIN_REQ;
            var t: time = 55;
            var tmp := deep_copy(gp);                        
            var status := isocket$.nb_transport_fw(gp,phase,t);
            message(LOW,append("After nb_transport_fw status = ",status));
            ind += 1;
        };
    };
    
    create_trans(base:uint, cmd: tlm_command) : tlm_generic_payload is {
        
        message(LOW,append("Creating gp with base = ",base));
        
        result = new;
        
        result.m_address = base*1000+base*100+base*10+base;
        result.m_command = cmd;
        for i from 0 to base do {
             result.m_data.add(i);
        };
        result.m_length = result.m_data.size();
        result.m_response_status = TLM_OK_RESPONSE;
        for i from base down to 0 do{
            result.m_byte_enable.add(0xff);
        };
        result.m_byte_enable_length = result.m_byte_enable.size();
    };
    
    nb_transport_bw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
        message(LOW,"Starting nb_transport_bw");
        message(LOW,"End of nb_transport_bw");
        return TLM_ACCEPTED;
    };
    
};

extend sys {
    producer is instance;
};

'>