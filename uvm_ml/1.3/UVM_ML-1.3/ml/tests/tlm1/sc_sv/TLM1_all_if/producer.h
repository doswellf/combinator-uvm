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

#include "packet.h"

#include "uvm_ml.h"

using namespace tlm;

template <typename T>
class producer : public uvm_component 
               , tlm_blocking_put_if<T> 
{
public:
  sc_port<tlm_blocking_put_if<T> > put_port;
  sc_port<tlm_blocking_get_if<T> > get_port;
  sc_port<tlm_blocking_peek_if<T> > peek_port;
  sc_port<tlm_transport_if<T, T> > trans_port;
  sc_port<tlm_nonblocking_put_if<T> > put_nb_port;
  sc_port<tlm_nonblocking_get_if<T> > get_nb_port;
  sc_port<tlm_nonblocking_peek_if<T> > peek_nb_port;
  sc_port<tlm_analysis_if<T>, 2, SC_ONE_OR_MORE_BOUND > a_port;
  sc_export<tlm_blocking_put_if<T> > put_export;

  producer(sc_module_name nm) : uvm_component(nm)
    , put_port("put_port")
    , get_port("get_port")
    , peek_port("peek_port")
    , trans_port("trans_port")
    , put_nb_port("put_nb_port")
    , get_nb_port("get_nb_port")
    , peek_nb_port("peek_nb_port")
    , a_port("a_port")
    , put_export("put_export")
  { 
    put_export(*this);
  }
  UVM_COMPONENT_UTILS(producer)
  void build() {
    cout << "SC producer::build" << endl;
  }
  virtual void put( const T& t1 ) {
    T * t;
    T rsp;
    T req;
    sc_time time;
    sc_time* one;
    t = new T;
    one = new sc_time(1,SC_NS);
    
    cout << "*** Blocking transactions from SC" << endl;
    cout << "[SC " << sc_time_stamp() << "] producer::sending T " << *t << endl;
    time = sc_time_stamp();
    put_port->put(*t);
    cout << "[SC " << sc_time_stamp() << "] producer::sent T " << *t << endl;
    sc_assert(t->data == 17);
    sc_assert(sc_time_stamp() == time+*one);
	      
    wait(4, SC_NS);
    cout << "[SC " << sc_time_stamp() << "] producer::getting " << endl;
    time = sc_time_stamp();
    get_port->get(*t);
    cout << "[SC " << sc_time_stamp() << "] producer::got T " << *t << endl;
    sc_assert (t->data == 18);
    sc_assert(sc_time_stamp() == time+*one);
    
    wait(4, SC_NS);
    cout << "[SC " << sc_time_stamp() << "] producer::peeking " << endl;
    time = sc_time_stamp();
    peek_port->peek(*t);
    cout << "[SC " << sc_time_stamp() << "] producer::peek T " << *t << endl;
    sc_assert (t->data == 18);
    sc_assert(sc_time_stamp() == time+*one);
    
    wait(4, SC_NS);
    req.data = t->data+1;
    cout << "[SC " << sc_time_stamp() << "] producer::transport " << req << endl;
    time = sc_time_stamp();
    rsp = trans_port->transport(req);
    cout << "[SC " << sc_time_stamp() << "] producer::transport response " << rsp << endl;
    sc_assert(rsp.data == 20);
    sc_assert(sc_time_stamp() == time+*one);
  }
  void run() {
    T * t;
    T rsp;
    T req;
    bool ret;
    cout << "[SC " << sc_time_stamp() << " ] producer::starting thread_proc" << endl;
    t = new T;
    for(int i = 0; i < 1; i++) {
      cout << "*** Nonblocking transactions from SC" << endl;

      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::can_put " << endl;
      ret = put_nb_port->nb_can_put();
      cout << "[SC " << sc_time_stamp() << "] producer::can_put returned " << ret << endl;
      sc_assert(ret == 1);

      wait(5, SC_NS);
      t->data = 17+i;
      cout << "[SC " << sc_time_stamp() << "] producer::sending packet " << *t << endl;
      ret = put_nb_port->nb_put(*t);
      cout << "[SC " << sc_time_stamp() << "] producer::sent packet " << *t << endl;
      sc_assert(ret == 1);

      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::can_get " << ret << endl;
      ret = get_nb_port->nb_can_get();
      cout << "[SC " << sc_time_stamp() << "] producer::can_get returned " << ret << endl;
      sc_assert(ret == 1);
      
      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::getting packet " << *t << endl;
      get_nb_port->nb_get(*t);
      cout << "[SC " << sc_time_stamp() << "] producer::got packet " << *t << endl;
      sc_assert(t->data == 17+1+i);
      
      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::can_peek " << endl;
      ret = peek_nb_port->nb_can_peek();
      cout << "[SC " << sc_time_stamp() << "] producer::can_peek returned " << ret << endl;
      sc_assert(ret == 1);
      
      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::peeking " << endl;
      peek_nb_port->nb_peek(*t);
      cout << "[SC " << sc_time_stamp() << "] producer::got packet " << *t << endl;
      sc_assert(t->data == 17+1);
      
      wait(5, SC_NS);
      cout << "[SC " << sc_time_stamp() << "] producer::analysis " <<  *t << endl;
      a_port->write(*t);
      cout << "[SC " << sc_time_stamp() << "] producer::analysis returned" <<  *t << endl;
      wait(5, SC_NS);
    }
    wait(2, SC_NS);
    cout << "[SC " << sc_time_stamp() << "] producer::done thread_proc" << endl;
  }
};

