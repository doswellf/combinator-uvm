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
// SV is the top component and it creates an e subtree from its env
<'
import dt;


unit my_unit {
    keep agent() == "SV";
    
    conf_data : data;
    keep uvm_config_get(conf_data);

    conf_pdata: pdata;
    keep uvm_config_get(conf_pdata);
    
    post_generate() is also {
        out("[SN] post_generate()");
        
        print conf_data;
        
        check that conf_data.addr == 10;
        check that conf_data.trailer == 20;
        check that conf_data.txt == "config object message";
        
        print conf_pdata;
        
        check that conf_pdata.data == 30;
        check that conf_pdata.addr == 4;
        check that conf_pdata.payload == 50;
    };
    
    run() is also {
        out("[SN] run()");
        start tcm();
    };
    
    tcm()@sys.any is {
        wait delay (500);
    };
    
    check() is also {
        out("TEST PASSED");
    };

};

'>
