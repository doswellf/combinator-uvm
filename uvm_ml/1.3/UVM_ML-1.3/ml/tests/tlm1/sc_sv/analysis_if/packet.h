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
#ifndef PACKET_H
#define PACKET_H

#include "uvm_ml.h"

/////////////////

class packet : public uvm_object {
public:
  UVM_OBJECT_UTILS(packet)
    packet() { data = 17; kind = 0;}
  packet(int i) { data = i; kind = 0;}
  virtual ~packet() { }

  virtual void do_print(ostream& os) const {
    os << "packet: " << data << endl;
  }
  virtual void do_pack(uvm_packer& p) const {
    p << data<<kind;
  }
  virtual void do_unpack(uvm_packer& p) {
    p >> data;
    p >> kind;
  }
  virtual void do_copy(const uvm_object* rhs) {
    const packet* drhs = DCAST<const packet*>(rhs);
    if (!drhs) { cerr << "ERROR in do_copy" << endl; return; }
    data = drhs->data;
  }
  virtual bool do_compare(const uvm_object* rhs) const {
    const packet* drhs = DCAST<const packet*>(rhs);
    if (!drhs) { cerr << "ERROR in do_compare" << endl; return true; }
    if (!(data == drhs->data)) return false;
    return true;
  }
  virtual bool check_data(int d) {
    cout << "CHECKING data of recived packet, expecting "<<d<<endl;
    return data == d;
  }
  
public:
  int data;
  bool kind;
};
UVM_OBJECT_REGISTER(packet)

/////////////////

#endif

