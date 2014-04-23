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

// Memory manager for tlm_generic_payload
template <typename GP_TYPE = tlm::tlm_generic_payload>
class mm: public tlm::tlm_mm_interface
{

public:
  mm() : free_list(0)
  {}

  GP_TYPE* allocate() {
    GP_TYPE* ptr;
    if (!free_list.empty()) {
      ptr = free_list.back();
      free_list.pop_back();
    } else {
      ptr = new GP_TYPE(this);
    }
    return ptr;
  }

  void free(tlm::tlm_generic_payload* trans) {
    trans->reset();
    free_list.push_back((GP_TYPE*)trans);
  }

private:
  std::vector<GP_TYPE*> free_list;
};


// Producer class produces TLM2 transactions
class producer: public uvm_component 
              , public tlm::tlm_bw_transport_if<tlm::tlm_base_protocol_types>
{
public:
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> b_isocket;
  tlm::tlm_initiator_socket<32,tlm::tlm_base_protocol_types> nb_isocket;
  int address;

  producer(sc_module_name nm) : uvm_component(nm)
                              , b_isocket("b_isocket")
			      , nb_isocket("nb_isocket")
  {
    cout << "SC producer::producer name= " << this->name() << endl;
    b_isocket(*this);
    nb_isocket(*this);
  }

  UVM_COMPONENT_UTILS(producer)

  // not implemented
  tlm::tlm_sync_enum nb_transport_bw(tlm_generic_payload& trans, tlm::tlm_phase& phase, sc_time& delay ) {
    cout << "[SC " << sc_time_stamp() <<"] nb_transport_bw " << endl;
    return tlm::TLM_COMPLETED;
  }

  void invalidate_direct_mem_ptr(sc_dt::uint64 start_range, sc_dt::uint64 end_range){};

  void run() {
    tlm_generic_payload* tgp;
    tlm_phase            phase = tlm::BEGIN_REQ;
    sc_time              delay((sc_dt::uint64)2,true);
    int                  addr;
    mm<tlm_generic_payload> mem_manager;

    tgp = mem_manager.allocate();
    tgp->acquire();
    wait(30, SC_NS);
    addr = address;
    create_trans(addr,tgp,tlm::TLM_WRITE_COMMAND);
    cout << "[SC " << sc_time_stamp() << "] producer::b_transport";
    print_gp(*tgp);
    b_isocket->b_transport(*tgp, delay);
    //nb_isocket->nb_transport_fw(*tgp, phase, delay);
    cout << "[SC " << sc_time_stamp() << "] producer::b_transport done";
    print_gp(*tgp);

    wait(8, SC_NS);
    create_trans(addr,tgp,tlm::TLM_READ_COMMAND);
    cout << "[SC " << sc_time_stamp() << "] producer::b_transport";
    print_gp(*tgp);
    b_isocket->b_transport(*tgp, delay);
    //nb_isocket->nb_transport_fw(*tgp, phase, delay);
    cout << "[SC " << sc_time_stamp() << "] producer::b_transport done";
    print_gp(*tgp);
  }
  void build() { 
    cout << "SC producer::build " << this->name() << endl;
    get_config_int("address", address);
  }
  void before_end_of_elaboration() {
    cout << "SC producer::before_end_of_elaboration " << this->name() << endl;
  }
  void connect() { 
    cout << "SC producer::connect " << this->name() << endl;
  }
  void end_of_elaboration() { 
    cout << "SC producer::end_of_elaboration " << this->name() << endl;
  }
  void start_of_simulation() { 
    cout << "SC producer::start_of_simulation " << this->name() << endl;
  }

  void create_trans(int addr, tlm_generic_payload* trans, tlm::tlm_command cmd) {
    int i;
    int length = 4;
    unsigned char *data;

    data = new unsigned char[length];
    unsigned char byte_enable[length];
    trans->set_address(addr);
    trans->set_command(cmd);
    for (i=0; i<length; i++){
      if(cmd == TLM_WRITE_COMMAND)
	data[i] = rand();
      else
	data[i] = 0;
    };
    trans->set_data_ptr(&data[0]);
    trans->set_data_length(length);
    trans->set_response_status(tlm::TLM_INCOMPLETE_RESPONSE);
    for (i=0; i<length; i++){
      byte_enable[i] = 0;
    };
    trans->set_byte_enable_ptr(&byte_enable[0]);
    trans->set_byte_enable_length(0);  
  }  

  // print content of generic payload
  void print_gp(tlm_generic_payload& gp){
    int i;
    unsigned char * data;
    
    data = gp.get_data_ptr();
    if(gp.get_command() == TLM_READ_COMMAND) cout << " TLM_READ_COMMAND";
    if(gp.get_command() == TLM_WRITE_COMMAND) cout << " TLM_WRITE_COMMAND";
    cout<< " address = " << hex << gp.get_address() << " data_length = "<<gp.get_data_length() << " m_data = ";
    
    for (i = 0; i<(int)gp.get_data_length(); i++){
      cout << hex << (int)(*data++);
      cout<< " ";
    };
    cout << " status= " << gp.get_response_status() << endl;
  }
};

UVM_COMPONENT_REGISTER(producer)

