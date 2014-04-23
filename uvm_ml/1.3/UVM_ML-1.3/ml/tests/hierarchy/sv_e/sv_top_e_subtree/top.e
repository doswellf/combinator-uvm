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
   
// Test demonstrates hierarchical construction
// SV is the top component and it creates an e subtree from its env
<'
import packet;


unit my_unit {
    keep agent() == "SV";
    //keep hdl_path() == "test.sv_env";
    inport : in interface_port of tlm_analysis of (packet) is instance;
       keep bind(inport,external);
    outport : out interface_port of tlm_analysis of (packet) is instance;
       keep bind(outport,external);

    pre_generate() is also {
        out("[SN] pre_generate()");
        print me.e_path();
        print me.get_parent_unit();
    };
    
    post_generate() is also {
        out("[SN] post_generate()");
        print me.e_path();
        print me.get_parent_unit();
    };
    
    connect_ports() is also {
        out("[SN] connect_ports()");
    };
    
    run() is also {
        out("[SN] run()");
        start tcm();
    };
    
    tcm()@sys.any is {
       var p : packet;
       //gen p;
       //p = new;
       wait delay (50);
       
       for i from 0 to 4 {
         // p.data = 17+i;
          gen p keeping {.data == i+17};
          out("[SN] sending packet ", p.data);
          outport$.write(p);
          wait delay (10);
       }; // for i from 1 to...
       //stop_run();
    };
    
    data_ref: int;
    keep data_ref == 101;
    
    write(p:packet) is {
        out(append("[SN] Got packet p.data = ",p.data));
        check that p.data == data_ref;
        data_ref+=1;
    };
    
    check() is also {
        out("[SN] check()");
        check that data_ref == 106;
        out("TEST PASSED");
    };

};

'>
