#ifndef PACKET_H
#define PACKET_H

#include "uvm_ml.h"
using namespace tlm;
using namespace uvm;

/////////////////

class packet : public uvm_object {
public:
  UVM_OBJECT_UTILS(packet)
  packet() { data = 17; }
  packet(int i) { data = i; }
  virtual ~packet() { }

  virtual void do_print(ostream& os) const {
    os << "packet: " << data << endl;
  }
  virtual void do_pack(uvm_packer& p) const {
    p << data;
  }
  virtual void do_unpack(uvm_packer& p) {
    p >> data;
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
public:
  int data;
};
UVM_OBJECT_REGISTER(packet)

/////////////////

#endif

