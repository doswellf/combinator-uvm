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
unit consumer {
    // SV interface
    b_tsocket     : tlm_target_socket of tlm_generic_payload 
      using prefix=sv_ is instance;
    nb_tsocket    : tlm_target_socket of tlm_generic_payload 
      using prefix=sv_ is instance;
    b_put_in_port : in interface_port of tlm_put of packet 
      using prefix=sv_ is instance;
      keep bind(b_put_in_port,external);
    nb_put_in_port: in interface_port of tlm_put of packet 
      using prefix=sv_ is instance;
      keep bind(nb_put_in_port,external);
    // SC interface
    b_sc_tsocket     : tlm_target_socket of tlm_generic_payload 
      using prefix=sc_ is instance;
    b_sc_put_in_port : in interface_port of tlm_put of packet 
      using prefix=sc_ is instance;
      keep bind(b_sc_put_in_port,external);
    nb_sc_put_in_port: in interface_port of tlm_put of packet 
      using prefix=sc_ is instance;
      keep bind(nb_sc_put_in_port,external);
    save: list of int;
   
   connect_ports() is also {
      b_tsocket.connect(external);
      nb_tsocket.connect(external);
      b_sc_tsocket.connect(external);
   };
   
    // Implementation for SV interfaces
    sv_nb_transport_fw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
       if(trans.m_command == TLM_WRITE_COMMAND) then {
          message(LOW,"Received nb_transport_fw WRITE ", hex(trans.m_data));
          save.clear();
          for i from 0 to trans.m_length-1 do {
             save.push(trans.m_data[i]);
          }; // for i from 0 to...
       } else {
          for i from 0 to trans.m_length-1 do {
             trans.m_data[i] = save.pop0();
          }; // for i from 0 to...         
          message(LOW,"Received nb_transport_fw READ ", hex(trans.m_data));
       };
       trans.m_response_status = TLM_OK_RESPONSE;
       return TLM_COMPLETED;
    };
    
    sv_b_transport(trans: tlm_generic_payload, t: *time)@sys.any is {
       if(trans.m_command == TLM_WRITE_COMMAND) then {
          message(LOW,"Received b_transport WRITE ", hex(trans.m_data));
          save.clear();
          for i from 0 to trans.m_length-1 do {
             save.push(trans.m_data[i]);
          }; // for i from 0 to...
       } else {
          for i from 0 to trans.m_length-1 do {
             trans.m_data[i] = save.pop0();
          }; // for i from 0 to...         
          message(LOW,"Received b_transport READ ", hex(trans.m_data));
       };
       trans.m_response_status = TLM_OK_RESPONSE;
       wait delay(5);
    };
    
    sv_transport_dbg(trans: tlm_generic_payload) : uint is  {
       message(LOW,"Received transport_dbg ", trans);
    };
    
    sv_put(p : packet)@sys.any is {
       message(LOW,"Received put ", p);      
       wait delay(5);
    };
    
    sv_try_put(p: packet) : bool is {
       message(LOW,"Received try_put ", p);      
    };
    
    sv_can_put() : bool is {
       message(LOW,"Received can_put ");      
    };
    
    sv_ok_to_put() : tlm_event is {
       message(LOW,"Received ok_to_put ");      
    };
   
    
    // Implementation for SC interfaces
    sc_nb_transport_fw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
       if(trans.m_command == TLM_WRITE_COMMAND) then {
          message(LOW,"Received nb_transport_fw WRITE ", trans.m_data);
          save.clear();
          for i from 0 to trans.m_length-1 do {
             save.push(trans.m_data[i]);
          }; // for i from 0 to...
       } else {
          for i from 0 to trans.m_length-1 do {
             trans.m_data[i] = save.pop0();
          }; // for i from 0 to...         
          message(LOW,"Received nb_transport_fw READ ", hex(trans.m_data));
       };
       trans.m_response_status = TLM_OK_RESPONSE;
       return TLM_COMPLETED;
    };
    
    sc_b_transport(trans: tlm_generic_payload, t: *time) @sys.any is {
       if(trans.m_command == TLM_WRITE_COMMAND) then {
          message(LOW,"Received b_transport WRITE ", hex(trans.m_data));
          save.clear();
          for i from 0 to trans.m_length-1 do {
             save.push(trans.m_data[i]);
          }; // for i from 0 to...
       } else {
          for i from 0 to trans.m_length-1 do {
             trans.m_data[i] = save.pop0();
          }; // for i from 0 to...         
          message(LOW,"Received b_transport READ ", hex(trans.m_data));
       };
       trans.m_response_status = TLM_OK_RESPONSE;
       wait delay(5);
    };
    
    sc_transport_dbg(trans: tlm_generic_payload) : uint is  {
       message(LOW,"Received transport_dbg ", trans);
    }; // transport_dbg
    
    sc_put(p : packet)@sys.any is {
       message(LOW,"Received put ", p);      
       wait delay(5);
    };
    
    sc_try_put(p: packet) : bool is {
       message(LOW,"Received try_put ", p);      
    };
    
    sc_can_put() : bool is {
       message(LOW,"Received can_put ");      
    };
    
    sc_ok_to_put() : tlm_event is {
       message(LOW,"Received ok_to_put ");      
    };
   
}; // unit consumer
'>