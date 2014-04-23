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

import env.e;

unit testbench {
   env is instance;   
   // Foreign (SV) child
   sv_child: any_unit is instance;
      keep sv_child != NULL;
      keep type sv_child is a child_component_proxy;
      keep sv_child.type_name == "SV:env";

   keep uvm_config_set("*producer", "address", 0x1000);
}; // unit testbench

extend sys {
   testbench is instance;
};

'>
