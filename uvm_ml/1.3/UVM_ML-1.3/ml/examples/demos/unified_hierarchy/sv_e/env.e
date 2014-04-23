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

import uvm_e/e/uvm_e_top.e;
import producer.e;
import consumer.e;
type env_type : [PASSIVE,ACTIVE];

unit env like uvm_env {
   keep agent() == "SV";
   e_active: env_type;
      keep uvm_config_get(e_active);
      keep soft e_active == PASSIVE;
   
   when ACTIVE {
      producer is instance;
   };
   consumer is instance;

   connect_ports() is also {
      consumer.b_tsocket.connect(external);
      consumer.nb_tsocket.connect(external);
   };
   when ACTIVE {
      connect_ports() is also {
         producer.b_socket.connect(external);
         producer.nb_socket.connect(external);
      };
   };
    
   when PASSIVE {
      run() is also {
         start keep_alive(); // avoid premature termination
      };
      keep_alive()@sys.any is {
         wait delay (100);      
      };
   };
   
}; // unit env

'>
