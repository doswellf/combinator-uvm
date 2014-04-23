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
using namespace tlm;


template <class T>
class consumer : public uvm_component 
               , tlm_blocking_put_if<T> 
               , tlm_blocking_get_if<T> 
	       , tlm_transport_if<T,T> 
	       , tlm_nonblocking_put_if<T> 
	       , tlm_nonblocking_get_if<T> 
	       , tlm_nonblocking_peek_if<T> 
	       , tlm_analysis_port<T>
	       , tlm_blocking_peek_if<T>
{
public:
  sc_export<tlm_blocking_put_if<T> > put_export;
  sc_export<tlm_blocking_get_if<T> > get_export;
  sc_export<tlm_blocking_peek_if<T> > peek_export;
  sc_export<tlm_transport_if<T,T> > trans_export;
  sc_export<tlm_nonblocking_put_if<T> > put_nb_export;
  sc_export<tlm_nonblocking_get_if<T> > get_nb_export;
  sc_export<tlm_nonblocking_peek_if<T> > peek_nb_export;
  sc_export<tlm_analysis_if<T> > a_export;

  consumer(sc_module_name nm) : uvm_component(nm)
			      , put_export("put_export")
			      , get_export("get_export")
			      , peek_export("peek_export")
			      , trans_export("trans_export")
                              , put_nb_export("put_nb_export")
			      , get_nb_export("get_nb_export")
			      , peek_nb_export("peek_nb_export")
			      , a_export("a_export")
  { 
    put_export(*this);
    get_export(*this);
    trans_export(*this);
    peek_export(*this);
    put_nb_export(*this);
    get_nb_export(*this);
    peek_nb_export(*this);
    a_export(*this);
    check_sum = 0;
  }

  UVM_COMPONENT_UTILS(consumer)

  void build() {
    cout << "SC consumer::build" << endl;
  }

  virtual void put( const T& t ) {
    cout << "[SC " << sc_time_stamp() << "] consumer::put: " << t << endl;
    save = t.data;
    assert (t.data == 21);
    wait(1, SC_NS);
    cout << "[SC " << sc_time_stamp() << "] consumer::put done " << endl;
    check_sum++;
  }

  virtual T get( tlm_tag<T> *t ) {
    T tmp;
    tmp.data = save+1;
    cout << "[SC " << sc_time_stamp() << "] consumer::get : " << tmp << endl;
    wait(1,SC_NS);
    cout << "[SC " << sc_time_stamp() << "] consumer::get done " << endl;
    check_sum = check_sum+1;
    return tmp;
  }

  virtual T peek( tlm_tag<T> *t ) const {
    T tt;
    cout << "[SC " << sc_time_stamp() << "] consumer::peek " << endl;
    tt.data = 21;
    cout << "[SC " << sc_time_stamp() << "] consumer::peek done " << endl;
    //check_sum = check_sum+1;
    return  tt;
  }

  virtual T transport( const T & req) {
    cout << "[SC " << sc_time_stamp() << "] consumer::transport : " << req << endl;
    T rsp;
    save = req.data;
    rsp.data = save+1;
    assert(req.data==19);
    wait(1,SC_NS);
    cout << "[SC " << sc_time_stamp() << "] consumer::transport done " << endl;
    check_sum = check_sum+1;
    return rsp; 
  }

  virtual bool nb_put( const T& t ) {
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_put: " << t << endl;
    save = t.data;
    sc_assert(save == 18);
    check_sum = check_sum+1;
    return true;
  }
  virtual bool nb_can_put( tlm_tag<T> *t ) const {
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_can_put" << endl;
    //    check_sum = check_sum+1;
    return true;
  }
  virtual const sc_event &ok_to_put( tlm_tag<T> *t ) const { 
    return dummy; 
  }

  virtual bool nb_get( T &t ) {
    T tmp;
    tmp.data = save+1;
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_get : " << tmp << endl;
    t = tmp;
    check_sum = check_sum+1;
    return true;
  }

  virtual bool nb_can_get( tlm_tag<T> *t ) const {
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_can_get " << endl;
    //    check_sum = check_sum+1;
    return true;
  }

  virtual const sc_event &ok_to_get( tlm_tag<T> *t ) const { 
    return dummy; 
  }

  virtual bool nb_peek(T &t) const {
    T tt;
    tt.data = save+1;
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_peek : " << tt << endl;
    t = tt;
    //check_sum = check_sum+1;
    return true;
  }
  virtual bool nb_can_peek( tlm_tag<T> *t ) const {
    cout << "[SC " << sc_time_stamp() << "] consumer::nb_can_peek " << endl;
    //check_sum = check_sum+1;
    return true;
  }
  virtual const sc_event &ok_to_peek( tlm_tag<T> *t ) const { return dummy; }

  void write(const T& t) {
    cout << "[SC " << sc_time_stamp() << "] consumer::write: " << t << endl;
    check_sum = check_sum+1;
    sc_assert(t.data==19);
  }

  sc_event dummy;
  int save;
  int check_sum;
};
