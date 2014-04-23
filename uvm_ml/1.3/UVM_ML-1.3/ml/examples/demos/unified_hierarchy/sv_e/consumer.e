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
    b_tsocket  : tlm_target_socket of tlm_generic_payload is instance;
    nb_tsocket : tlm_target_socket of tlm_generic_payload is instance;
    // Save data for read after write; address being ignored
    save       : list of int;
   
   // Implementation of blocking TLM2 transport
   b_transport(trans: tlm_generic_payload, t: *time)@sys.any is {
      if(trans.m_command == TLM_WRITE_COMMAND) then {
         message(LOW,"Received b_transport WRITE ", hex(trans.m_data));
         save.clear();
         for i from 0 to trans.m_length-1 do {
            save.push(trans.m_data[i]);
         }; // for i from 0 to...
      } else {
         message(LOW,"Received b_transport READ ", hex(trans.m_data));
         for i from 0 to trans.m_length-1 do {
            trans.m_data[i] = save.pop0();
         }; // for i from 0 to...         
      };
      trans.m_response_status = TLM_OK_RESPONSE;
      wait delay(t);
      t = 0;
   };
    
   // Implementation of non-blocking TLM2 transport
   nb_transport_fw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
      if(trans.m_command == TLM_WRITE_COMMAND) then {
         message(LOW,"Received nb_transport_fw WRITE ", hex(trans.m_data));
         save.clear();
         for i from 0 to trans.m_length-1 do {
            save.push(trans.m_data[i]);
         };
      } else {
         message(LOW,"Received nb_transport_fw READ ", hex(trans.m_data));
         for i from 0 to trans.m_length-1 do {
            trans.m_data[i] = save.pop0();
         };         
      };
      start nb_transport_response(trans, phase, t);
      trans.m_response_status = TLM_OK_RESPONSE;
      return TLM_ACCEPTED;
   };
   
   transport_dbg(trans: tlm_generic_payload) : uint is  {
      message(LOW,"Received transport_dbg ", trans);
   }; // transport_dbg

    // Respond to non-blocking call
    nb_transport_response(trans: tlm_generic_payload, phase: tlm_phase_enum, t: time)@sys.any is {
       var ph: tlm_phase_enum;
       
       message(LOW,"Starting nb_transport_response delay= ", t);        
       wait delay (t); // t is always 0
       t = 0;
       ph = BEGIN_RESP;
       compute nb_tsocket$.nb_transport_bw(trans, ph, t);    
       message(LOW,"Ending nb_transport_response");
    };
    
}; // unit consumer
'>