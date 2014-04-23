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
// e is the top component and it creates an SC subtree from its env
<'
import packet;


extend sys {
    u is instance;
};
    
    
unit u {
   keep agent() == "SV";
  
    inport :  in interface_port of tlm_analysis of (packet) is instance;
       keep bind(inport,external);
    outport : out interface_port of tlm_analysis of (packet) is instance;
       keep bind(outport,external);
    
    my_sc_child: child_component_proxy is instance;
    keep my_sc_child.type_name == "SC:sctop";
    
    pre_generate() is also {
        out("[SN] pre_generate()");
    };
    
    post_generate() is also {
        out("[SN] post_generate()");
    };
    
    connect_ports() is also {
        var sc_env := "sys.u.my_sc_child.sc_env.";
        out("[SN] connect_ports()");
        compute uvm_ml.connect_names("sys.u.outport", append(sc_env,"consumer.aexport"));
        compute uvm_ml.connect_names(append(sc_env,"producer.aport"), "sys.u.inport");
    };
    
    run() is also {
        out("[SN] run()");
        start tcm();
    };
    
    tcm()@sys.any is {
       var p : packet;
       p = new;

       for i from 0 to 4 {
          p.data = 17+i;
          out("[SN] sending packet ", p.data);
          outport$.write(p);
          wait delay (10);
       }; // for i from 1 to...
    };
    
    data_ref: int;
    keep data_ref == 17;
    
    write(p:packet) is {
        out(append("[SN] Got packet p.data = ",p.data));
        check that p.data == data_ref;
        data_ref+=1;
    };
    
    check() is also {
        out("[SN] check()");
        check that data_ref == 22;
        out("TEST PASSED");
    };

};

'>
