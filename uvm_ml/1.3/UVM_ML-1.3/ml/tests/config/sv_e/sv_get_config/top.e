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
   
// Test demonstrates configuration across unified hierarchy
// e is the top component and it creates an SV subtree from its env
<'
import dt;

extend sys {
    u is instance;
};

unit u {
    
    my_sv_child: any_unit is instance;
    keep soft my_sv_child == NULL;
    
    d : data;
    keep d.addr == 10;
    keep d.trailer == 20;
    keep d.txt == "config object msg";
    
    pd : pdata;
    keep pd.data == 30;
    keep pd.addr == 4;
    keep pd.payload == 50;
    
    keep uvm_config_set("my_sv_child","conf_data",d);
    keep uvm_config_set("my_sv_child","conf_pdata",pd);
        
    run() is also {
        out("[SN] run()");
        start tcm();
    };
    
    tcm()@sys.any is {
        wait delay (1000);
        stop_run();
    };
    
    check() is also {
        out("TEST PASSED");
    };

};

extend u {
    keep my_sv_child != NULL;
    keep type my_sv_child is a child_component_proxy;
    keep my_sv_child.type_name == "SV:test";
};
    
'>
