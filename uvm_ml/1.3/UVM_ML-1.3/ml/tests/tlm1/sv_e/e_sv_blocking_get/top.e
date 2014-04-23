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
import packet;
define <echocmd'action> "echocmd <any>" as {
    out("[SN] >>> ",sys.time,": executing ",str_expand_dots("<1>"));
    <1>;
};

unit client1 {
    p1 :  out interface_port of tlm_get of packet is instance;
    
    run() is also {
        start ver();
    };
    
    connect_ports() is also {
        p1.connect("test.top_env.monitor.b_in");
    };
    
    !completed_counter : uint;    
    ver()@sys.any is {
       raise_objection(TEST_DONE);

        wait delay(100);
        for i from 1 to 10 {
            out("------------------------------------------------------");
            var p : packet;
            var res : bool;
            echocmd res = p1$.try_get(p);

            out("Got res = ",res,", packet = ",p); 
            check that res;           
            check that p.data == i * 10;
            check that p.trailer == i * 20;
            check that p.txt == appendf("Iteration # %d",i);
           completed_counter+=1;
            wait delay(5);
        };
        print completed_counter;
        // now try_get should return 0
        for i from 1 to 10 {
            out("------------------------------------------------------");
            var p : packet = new;
            p.data = 11;
            p.trailer = 22;
            p.txt = "should stay like this";
            var p_copy := deep_copy(p);
            var res : bool;
            echocmd res = p1$.try_get(p);
            check that res == FALSE;
            out("Got packet = ",p);
            check that deep_compare(p,p_copy,1).is_empty();
           completed_counter+=1;
            wait delay(5);
        }; 
        print completed_counter;
        wait delay(10);
        echocmd check that p1$.can_get() == TRUE;
        echocmd check that p1$.can_get() == FALSE;
        echocmd check that p1$.can_get() == TRUE;
        echocmd check that p1$.can_get() == FALSE;
       completed_counter+=1;
       print completed_counter;
       var before := sys.time;
       for i from 11 to 20 {
          var p : packet;
          p1$.get(p);
          check that p.data == i*10;
          check that p.trailer == i*20;
          check that p.txt == appendf("Iteration # %0d",i);
          check that before+20 == sys.time;
          before+=20;
          completed_counter+=1;
       };
       print completed_counter;
       drop_objection(TEST_DONE);
    };
    check() is also {
        check that completed_counter == 31 else dut_error("completed_counter=",completed_counter);
        out("TEST PASSED");
    };
};
extend sys {
    c : client1 is instance;
};
'>




