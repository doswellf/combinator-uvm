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
   b_tsocket     : tlm_target_socket of tlm_generic_payload is instance;
   nb_tsocket    : tlm_target_socket of tlm_generic_payload is instance;
   b_put_in_port : in interface_port of tlm_put of packet is instance;
       keep bind(b_put_in_port,external);
   nb_put_in_port: in interface_port of tlm_put of packet is instance;
       keep bind(nb_put_in_port,external);
   
   connect_ports() is also {
      b_tsocket.connect(external);
      nb_tsocket.connect(external);
   };
   
   nb_transport_fw(trans: tlm_generic_payload, phase: *tlm_phase_enum, t: *time): tlm_sync_enum is {
      message(LOW,"Received nb_transport_fw ", trans.m_address, ": ", trans.m_data);
      return TLM_COMPLETED;
   };
   
   b_transport(trans: tlm_generic_payload, t: *time)@sys.any is {
      message(LOW,"Received b_transport_f ", trans.m_address, ": ", trans.m_data);
      wait delay(5);
   };
    
   transport_dbg(trans: tlm_generic_payload) : uint is  {
      message(LOW,"Received transport_dbg ", trans);
   }; // transport_dbg

   put(p : packet)@sys.any is {
      message(LOW,"Received put ", p);      
      wait delay(5);
   };
   try_put(p: packet) : bool is {
      message(LOW,"Received try_put ", p);      
   };
   can_put() : bool is {
      message(LOW,"Received can_put ");      
   };
   ok_to_put() : tlm_event is {
      message(LOW,"Received ok_to_put ");      
   };
   
}; // unit consumer
'>