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
// e is the top component and it creates an SV subtree from its env
<'
import packet;

extend sys {
    u is instance;
};

unit u {
  
    inport  :  in interface_port of tlm_analysis of (packet) is instance;
       keep bind(inport,external);
    outport : out interface_port of tlm_analysis of (packet) is instance;
       keep bind(outport,external);
    
    my_sv_child: any_unit is instance;
    keep soft my_sv_child == NULL;
    
    pre_generate() is also {
        out("[SN] pre_generate()");
    };
    
    post_generate() is also {
        out("[SN] post_generate()");
    };
    
    connect_ports() is also {
        out("[SN] connect_ports()");
        compute uvm_ml.connect_names("sys.u.outport", "sys.u.my_sv_child.sv_env.consumer.aimp");
        compute uvm_ml.connect_names("sys.u.my_sv_child.sv_env.producer.aport", "sys.u.inport");
    };
    
    run() is also {
        out("[SN] run()");
        start tcm();
    };
    
    tcm()@sys.any is {
       var p : packet;
       p = new;
       wait delay (50);
       
       for i from 0 to 4 {
          p.data = 17+i;
          out("[SN] sending packet ", p.data);
          outport$.write(p);
          wait delay (10);
       }; // for i from 1 to...
       stop_run();
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

extend u {
    keep my_sv_child != NULL;
    keep type my_sv_child is a child_component_proxy;
    keep my_sv_child.type_name == "SV:test";
};
    
'>
