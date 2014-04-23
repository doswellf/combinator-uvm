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
/*! \file ml_tlm2.cpp
  \brief Implementation of ML TLM2 functionality.
*/
#include "ml_tlm2.h"
#include "uvm_imp_spec_macros.h"

#include "uvm_ml_adapter_imp_spec_macros.h"
#include "common/uvm_ml_adapter.h"

#include <sstream>

namespace tlm {
/*! \class uvm_gp_wrapper_base
  \brief Base class for uvm_gp wrapper.

  
*/
  class uvm_gp_wrapper_base: public uvm_object {
  public:
    static int extensions_size(tlm_generic_payload * gp)
    {
      return gp->m_extensions.size();
    }
  };
}

namespace uvm_ml {

  uvm_ml_companion_map_type * uvm_ml_class_company::companion_map = NULL;

  ML_TLM2_GP_BEGIN(tlm_generic_payload) \
  ML_TLM2_GP_END(tlm_generic_payload)

  typedef map<std::string, std::string> ml_tlm2_socket_map_type;

  
  ml_tlm2_socket_map_type                 ml_tlm2_target_socket_map;
  ml_tlm2_socket_map_type                 ml_tlm2_init_socket_map;


  // nb transport fw/bw item mapping
  typedef map<unsigned int,tlm_generic_payload*>   ml_tlm2_transaction_mapping_map_type; 
  typedef map<tlm_generic_payload*,unsigned int>   ml_tlm2_id_mapping_map_type; 
  typedef map<std::string, bool>                   ml_tlm2_disable_transaction_mapping_map_type; 

  ml_tlm2_transaction_mapping_map_type           ml_tlm2_transaction_mapping_map;
  ml_tlm2_id_mapping_map_type                    ml_tlm2_id_mapping_map; 
  ml_tlm2_disable_transaction_mapping_map_type   ml_tlm2_disable_transaction_mapping_map;

void ml_tlm2_do_register_target(const std::string &target_socket_name, const std::string &transactor_name) {
    ml_tlm2_target_socket_map[target_socket_name] = target_socket_name;
}

void ml_tlm2_do_register_initiator(const std::string &initiator_socket_name, const std::string &transactor_name) {
    ml_tlm2_init_socket_map[initiator_socket_name] = initiator_socket_name;
}

extern void uvm_ml_do_connect (std::string port_name, std::string export_name);

bool ml_tlm2_check_cross_registration(const std::string & initiator_socket_name, const std::string & target_socket_name) { 
    if (ml_tlm2_target_socket_map[initiator_socket_name] != "") {
        string err_str = "In uvm_ml_connect(): The first argument (initiator socket path) '" + initiator_socket_name + "' was registered with ML_TLM2_REGISTER_TARGET";
        SC_REPORT_FATAL("Error", err_str.c_str());
        return false;
    }
    else if (ml_tlm2_init_socket_map[target_socket_name] != "") {
        string err_str = "In uvm_ml_connect(): The second argument (target socket path) '" + target_socket_name + "' was registered with ML_TLM2_REGISTER_INITIATOR";
        SC_REPORT_FATAL("Error", err_str.c_str());
        return false;
    }
    return true;
}

std::string ml_tlm2_relative_path(const std::string &cur_context_name, 
                                  const std::string &containing_module_name, 
                                  const std::string &socket_name) {

  if (containing_module_name == cur_context_name)
    return "";
  else
    if ((cur_context_name.size() < containing_module_name.size()) && (containing_module_name.compare(0,cur_context_name.size(), cur_context_name) == 0) && containing_module_name[cur_context_name.size()] == '.')
      return containing_module_name.substr(cur_context_name.size() + 1);
    else {
      string err_str = "ML TLM2 socket " + containing_module_name + "." + socket_name + " registration is not activated from an enclosing module";
      SC_REPORT_FATAL("Error", err_str.c_str());
    }
  return "INTERNAL ERROR";
}

std::string ml_tlm2_convertor_relative_name(const std::string &cur_context_name, 
                                            const std::string &containing_module_name, 
					    const std::string &socket_name) {
  const std::string &relative_path = ml_tlm2_relative_path(cur_context_name, containing_module_name, socket_name);
  if (relative_path != "")
    return (relative_path + "_" + socket_name + "_tlm2_convertor");
  else
    return(socket_name + "_tlm2_convertor");
}


void ml_tlm2_map_transaction(tlm_generic_payload * tlm_gp, unsigned int & transaction_id) {  
  // assign id if needed
  if (transaction_id == ML_TLM2_UNINITIALIZED_ID) {
    transaction_id = uvm_ml_utils::assign_transaction_id();
  }
  ml_tlm2_transaction_mapping_map[transaction_id] = tlm_gp;
  ml_tlm2_id_mapping_map[tlm_gp] = transaction_id;
  tlm_gp->acquire();
}
  
tlm_generic_payload *ml_tlm2_get_transaction_by_id(unsigned int id) {    
  map<unsigned int,tlm_generic_payload*>::iterator it = ml_tlm2_transaction_mapping_map.find(id);
  if (it == ml_tlm2_transaction_mapping_map.end()) {
    return 0;
  } else {
    return it->second;
  };
}

unsigned int ml_tlm2_get_id_by_transaction(tlm_generic_payload &trans) {
  map<tlm_generic_payload*, unsigned int>::iterator it = ml_tlm2_id_mapping_map.find(&trans);
  if (it == ml_tlm2_id_mapping_map.end()) {
    return ML_TLM2_UNINITIALIZED_ID;
  } else {
    return it->second;
  };
}

bool ml_tlm2_release_transaction(tlm_generic_payload * gp_ptr, unsigned int & transaction_id) {    
  //assert(gp_ptr != 0);
  if(gp_ptr == 0) {
    char msg[1024];
    sprintf(msg, "\nTransaction ID is '%s'\n", transaction_id);
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: ml_tlm2_release_transaction failed due to null pointer",msg);
    return false;
  };
  int result = ml_tlm2_id_mapping_map.erase(gp_ptr);
  if (result == 0) {
    return false;
  }
  result = ml_tlm2_transaction_mapping_map.erase(transaction_id);  
  if (result == 0) {
    return false;
  }  
  gp_ptr->release();  
  transaction_id = ML_TLM2_UNINITIALIZED_ID;
  return true;
}

void ml_tlm2_turn_off_transaction_mapping(const char* socket_name) {
  ml_tlm2_disable_transaction_mapping_map[socket_name] = true;
}

bool ml_tlm2_transaction_mapping_disabled(const string &socket_name) {
  if (ml_tlm2_disable_transaction_mapping_map.find(socket_name) == ml_tlm2_disable_transaction_mapping_map.end())
    return false;
  else
    return ml_tlm2_disable_transaction_mapping_map[socket_name];
}

const char* ml_tlm2_phase_to_string(tlm_phase phase) {
  switch (phase) {
  case BEGIN_REQ:
    return (const char*)"BEGIN_REQ";
  case END_REQ:
    return (const char*)"END_REQ";
  case BEGIN_RESP:
    return (const char*)"BEGIN_RESP";
  case END_RESP:
    return (const char*)"END_RESP";
  defualt:
    return (const char*)"invalid phase";
  }
  return (const char*)"";
}

const char* ml_tlm2_status_to_string(tlm_sync_enum status) {
  switch (status) {
  case TLM_COMPLETED:
    return (const char*)"TLM_COMPLETED";
  case TLM_ACCEPTED:
    return (const char*)"TLM_ACCEPTED";
  case TLM_UPDATED:
    return (const char*)"TLM_UPDATED";
  defualt:
    return (const char*)"invalid status";
  }
  return (const char*)"";
}

void ml_tlm2_transaction_mapping_update_error(const string &socket_name, 
					       const string &intf_name, 
					       tlm_phase phase) {
  string err_str = "ML-TLM2 non-blocking tranasaction did not follow the rules of the TLM2 standard.\n'" +  
    intf_name + "' of '" + socket_name + "' was called with phase '" + ml_tlm2_phase_to_string(phase) + 
    "', but the transaction was not first sent on \nthe forward path with the BEGIN_REQ phase, or already returned on the forward \n\
path with the END_RESP phase or the TLM_COMPLETED status.\n";
  SC_REPORT_FATAL("Error", err_str.c_str());
}

void ml_tlm2_transaction_mapping_remove_error(const string &socket_name, 
					       const string &intf_name, 
					       tlm_phase phase, 
					       tlm_sync_enum status) {
  string err_str = "ML-TLM2 non-blocking tranasaction did not follow the rules of the TLM2 standard.\n'" +  
    intf_name + "' of '" + socket_name + "' returned with phase '" + ml_tlm2_phase_to_string(phase) + "' and status '" + 
    ml_tlm2_status_to_string(status) + "', but the transaction was not first sent on \nthe forward path with the BEGIN_REQ phase, " + 
    "or already returned on the forward \npath with the END_RESP phase or the TLM_COMPLETED status.\n";
  SC_REPORT_FATAL("Error", err_str.c_str());
}

void ml_tlm2_transaction_mapping_mm_error(const string &socket_name) {
  string err_str = "ML-TLM2 non-blocking tranasaction does not have a memory manager, and therfore cannot be mappeed.\n Socket '" +  
    socket_name + "' has transaction mapping enabled in its connection method, but no memory manager exists for the transaction.\n " +
    "This is not supported.\n";
  SC_REPORT_FATAL("Error", err_str.c_str());  
}

//////////////////

uvm_ml_packer & operator << (uvm_ml_packer &p, tlm_generic_payload * tlm_gp) { 
  if (tlm_gp == NULL) { 
    p.pack_null(); 
  } 
  else { 
    uvm_ml_class_companion * companion = uvm_ml_class_company::get_companion(typeid(*tlm_gp)); 
    p.pack_obj_header(companion->get_type_name());		
    ml_tlm2_gp_companion::pack_tlm_generic_payload(p, tlm_gp);	
    companion->uvm_ml_automation(&p, tlm_gp, NULL, ML_TLM2_PACK_OP); 
  } 
  return p; 
} 

uvm_ml_packer & operator << (uvm_ml_packer &p, tlm_generic_payload & tlm_gp) { 
  uvm_ml_class_companion * companion = uvm_ml_class_company::get_companion(typeid(tlm_gp)); 
  //assert (companion != NULL);
  if(companion == NULL) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: packing failed due to unidentified type","");
  };
  p.pack_obj_header(companion->get_type_name());
  ml_tlm2_gp_companion::pack_tlm_generic_payload(p, &tlm_gp);	
  companion->uvm_ml_automation(&p, &tlm_gp, NULL, ML_TLM2_PACK_OP); 
  return p; 
}

uvm_ml_packer & operator >> (uvm_ml_packer &p, tlm_generic_payload *& tlm_gp) { 
  tlm_gp = (tlm_generic_payload *) p.unpack_obj_header();
  if (tlm_gp) { 
    uvm_ml_class_companion * companion = uvm_ml_class_company::get_companion(typeid(*tlm_gp)); 
    ml_tlm2_gp_companion::unpack_tlm_generic_payload(p, tlm_gp);	
    companion->uvm_ml_automation(&p, tlm_gp, NULL, ML_TLM2_UNPACK_OP); 
  } 
  return p; 
}

uvm_ml_packer & operator << (uvm_ml_packer &p, tlm_extension_base * ext) { 
  uvm_ml_class_companion * companion = uvm_ml_class_company::get_companion(typeid(*ext)); 
  p.pack_obj_header(companion->get_type_name());		
  companion->uvm_ml_automation(&p, ext, NULL, ML_TLM2_PACK_OP); 
  return p; 
} 

uvm_ml_packer & operator >> (uvm_ml_packer &p, tlm_extension_base *& ext) { 
  ext = (tlm_extension_base *) p.unpack_obj_header();
  if (ext) { 
    uvm_ml_class_companion * companion = uvm_ml_class_company::get_companion(typeid(*ext)); 
    companion->uvm_ml_automation(&p, ext, NULL, ML_TLM2_UNPACK_OP);
  } 
  return p; 
}

//////////////////

void ml_tlm2_pack(
  tlm_generic_payload & val,
  uvm_ml_packed_obj* p
) {
  //uvm_ml_packer pkr;
  static uvm_ml_packer& pkr = uvm_ml_packer::get_the_uvm_ml_packer();
  pkr << val;
  int packed_size = pkr.get_remaining_unpacked_bits();
  int max_size = uvm_ml::uvm_ml_utils::get_max_bits();
  if (packed_size > max_size) {
    char msg[1024];
    sprintf(msg,"\nuvm_object size is %d\n"
            "Max size is %d\n"
            "uvm_object type is '%s'\n"
            "Consider increasing the maximum size limit with the "
            "irun option '-defineall UVM_PACK_MAX_SIZE=<size>'.",
	    packed_size, max_size, ml_tlm2_class_company::get_type_name(typeid(val)).c_str()
           );
    UVM_ML_SC_REPORT_ERROR(ML_UVM_SIZE_LIMIT_,msg);
  }
  pkr.fill_uvm_ml_packed_obj(p);
  pkr.reset();
}

void ml_tlm2_unpack_create(
  uvm_ml_packed_obj* p,
  tlm_generic_payload*& val
) {
  try {
    static uvm_ml_packer& pkr = uvm_ml_packer::get_the_uvm_ml_packer();
    pkr.set_from_uvm_ml_packed_obj(p);
    pkr >> val;
    // check if any unpack error happened;
    // only 2 kinds of errors are flagged:
    // too few bits or too many bits;
    // check for too few bits here, for
    // too many bits exception is thrown
    // which needs to be caught
    if (int rem = pkr.get_remaining_unpacked_bits()) { // implies too few bits
      char msg[1024];
      sprintf(msg,"\nFewer bits unpacked in SystemC than were packed "
              "for this tlm_generic_payload in foreign language. "
              "This may be due to a mismatch in class definitions "
              "across languages - the SystemC "
              "tlm_generic_payload object is smaller in size\n"
              "tlm2 transaction type is '%s'\n"
              "Number of remaining bits is %d\n",
	      ml_tlm2_class_company::get_type_name(typeid(*val)).c_str(), rem 
             );
      SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    }
    pkr.reset();
  }
  // check if "too may bits" error happened
  catch( const sc_report& ex ) {
    if (strcmp(UVM_PACKER_UNPACK_INDEX_, ex.get_msg_type()) == 0) {
      // implies too may bits error
        UVM_ML_SC_PRINT_REPORT(ex);
      char msg[1024];
      sprintf(msg,"\nMore bits unpacked in SystemC than were packed "
              "for this uvm_object in foreign language. "
              "This may be due to a mismatch in class definitions "
              "across languages - the SystemC "
              "uvm_object is larger in size\n"
              "uvm_object type is '%s'\n",
	      ml_tlm2_class_company::get_type_name(typeid(*val)).c_str()
             );
      SC_REPORT_ERROR(UVM_PACKER_UNPACK_OBJECT_,msg);
    } else  {
      // not the error we are looking for, throw back
      throw(ex);
    }
  }
}

void ml_tlm2_update_data_from_response(tlm_generic_payload &trans, 
			               tlm_generic_payload &response_gp,
			               string full_socket_name) {
  unsigned int length = response_gp.get_data_length();
  if (trans.get_data_length() != length) {
    string str = full_socket_name + ": " + "data_lengths in request and response transactions are different";
    SC_REPORT_FATAL("Error", str.c_str());
  }
  if (length > 0 && response_gp.get_data_ptr())
    memcpy(trans.get_data_ptr(), response_gp.get_data_ptr(), length);
}

//////////////////

void ml_tlm2_bw_update_gp(tlm_generic_payload & tlm_gp, tlm_generic_payload & other) 
{
  uvm_ml_class_company::update_class(typeid(tlm_gp), &tlm_gp, &other);
}

//////////////////

uvm_ml_class_companion::uvm_ml_class_companion(const string & name) 
{
  m_type_name = name;
}

uvm_ml_class_companion::~uvm_ml_class_companion()
{
}

ml_tlm2_gp_companion::~ml_tlm2_gp_companion()
{
}

ml_tlm2_ext_companion::~ml_tlm2_ext_companion()
{
}

void ml_tlm2_gp_companion::update(void * target, void * src)
{
  update_tlm_generic_payload((tlm_generic_payload *) target, (tlm_generic_payload *) src);
  uvm_ml_automation(NULL, target, src, ML_TLM2_BW_UPDATE_OP);
}

void ml_tlm2_ext_companion::update(void * ext, void * tlm_gp)
{
  tlm_extension_base * other_ext = get_other_ext((tlm_generic_payload *) tlm_gp);
  if (other_ext != NULL)
    uvm_ml_automation(NULL, ext, other_ext, ML_TLM2_BW_UPDATE_OP);
}

uvm_ml_companion_map_type & uvm_ml_class_company::get_companion_map() 
{ 
    if (companion_map == NULL)
      companion_map = new uvm_ml_companion_map_type();

    return *companion_map; 
}

bool uvm_ml_class_company::register_class_companion(const type_info & actual_type, uvm_ml_class_companion * c) 
{
    uvm_ml_companion_map_type & map = get_companion_map();
    if (map[&actual_type] == 0) {
	map[&actual_type] = c;
	uvm_factory::register_class_creator(c->get_type_name(), c);
    } else
      delete c; // Otherwise there will be memory leak
    
    return true; // dummy return value needed to enable the function call in an initializer
}
  
uvm_ml_class_companion * uvm_ml_class_company::get_companion(const type_info & actual_type) 
{
    uvm_ml_companion_map_type & map = get_companion_map();
    uvm_ml_class_companion * c = map[&actual_type];
    if (c == NULL) {
      string err_str = "Class with type_info.name() " + string(actual_type.name()) + " was not registered via ML_TLM2_GP_BEGIN or ML_TLM2_GP_EXT_BEGIN macro";
      SC_REPORT_FATAL("Error", err_str.c_str());
    }
    return c;
}

string uvm_ml_class_company::get_type_name(const type_info & actual_type)
{
    uvm_ml_class_companion * comp = get_companion(actual_type);
    if (comp == NULL) {
      string err_str = "Class with type_info.name() " + string(actual_type.name()) + " was not registered via ML_TLM2_GP_BEGIN or ML_TLM2_GP_EXT_BEGIN macro";
      SC_REPORT_FATAL("Error", err_str.c_str());
      return "";
    }
    return comp->get_type_name();
}

void uvm_ml_class_company::update_class(const type_info & actual_type, void * target, void * src)
{
    uvm_ml_class_companion * comp = get_companion(actual_type);
    if (comp == NULL) {
      string err_str = "Class with type_info.name() " + string(actual_type.name()) + " was not registered via ML_TLM2_GP_BEGIN or ML_TLM2_GP_EXT_BEGIN macro";
      SC_REPORT_FATAL("Error", err_str.c_str());
      return;
    }
    comp->update(target, src);
}

ml_tlm2_ext_companion * ml_tlm2_class_company::get_ext_companion(const type_info & actual_type) 
{
    uvm_ml_class_companion * comp = get_companion(actual_type);
    ml_tlm2_ext_companion * ret = dynamic_cast<ml_tlm2_ext_companion *>(comp);
    return ret;
}

void ml_tlm2_gp_companion::update_tlm_generic_payload(tlm_generic_payload * tlm_gp, tlm_generic_payload * other) 
{  
  // update response status
  tlm_gp->set_response_status(other->get_response_status());

  // update dmi
  tlm_gp->set_dmi_allowed(other->is_dmi_allowed());

  // update extensions   
  for (unsigned int j = 0; j < uvm_gp_wrapper_base::extensions_size(tlm_gp); j++) {
    tlm_extension_base * ext = tlm_gp->get_extension(j);
    if (ext) {
      ml_tlm2_ext_companion * ext_comp = ml_tlm2_class_company::get_ext_companion(typeid(*ext));
      ext_comp->update(ext, other);
    }
  }  
}

void ml_tlm2_gp_companion::pack_tlm_generic_payload(uvm_ml_packer& p, tlm_generic_payload * tlm_gp) 
{
    tlm_extension_base * i_extension;
    unsigned int         i_extension_num = 0;
  
    if(tlm_gp == NULL) SC_REPORT_FATAL("Error", "pack_tlm_generic_payload called with tlm_gp NULL");
    p << tlm_gp->get_address() << tlm_gp->get_command();
    p << tlm_gp->get_data_length();
    for (unsigned j = 0; j < tlm_gp->get_data_length(); j++) {
      p << (tlm_gp->get_data_ptr())[j];
    }
    p << tlm_gp->get_data_length() << tlm_gp->get_response_status();

    p << tlm_gp->is_dmi_allowed();
  
    p << tlm_gp->get_byte_enable_length();
    for (unsigned j = 0; j < tlm_gp->get_byte_enable_length(); j++) {
      p << (tlm_gp->get_byte_enable_ptr())[j];
    }
  
    p << tlm_gp->get_byte_enable_length() << tlm_gp->get_streaming_width();
    for (unsigned int j = 0; j < uvm_gp_wrapper_base::extensions_size(tlm_gp); j++) {
      if (tlm_gp->get_extension(j))
	i_extension_num++;
    }
    p << i_extension_num;
    for (unsigned int j = 0; j < uvm_gp_wrapper_base::extensions_size(tlm_gp); j++) {
      i_extension = tlm_gp->get_extension(j);
      if (i_extension) {
	// Size does not count the actual extensions
	p << i_extension;
      }
    }
}

void ml_tlm2_gp_companion::unpack_tlm_generic_payload(uvm_ml_packer& p, tlm_generic_payload * tlm_gp) 
{
    sc_dt::uint64        i_m_address;
    int                  i_m_command;
    unsigned char*       i_m_data = 0;
    unsigned int         i_m_length;
    int                  i_m_response_status;
    bool                 i_m_dmi;
    unsigned char*       i_m_byte_enable = 0;
    unsigned int         i_m_byte_enable_length;
    unsigned int         i_m_streaming_width;
  
    unsigned int         length;
    unsigned int         i_extensions_size;
    tlm_extension_base * i_extension;
    stringstream msg;
  
    p >> i_m_address;
    tlm_gp->set_address(i_m_address);
  
    p >> i_m_command;
    tlm_gp->set_command(tlm_command(i_m_command));
  
    p >> length;
    if (length)
      i_m_data = new unsigned char [length];
    for (unsigned j = 0; j < length; j++)
      p >> i_m_data[j];
    tlm_gp->set_data_ptr(i_m_data);
  
    p >> i_m_length;
    msg << "do_unpack called with data length " << length << " different from m_length " << i_m_length;
    if(length != i_m_length) SC_REPORT_FATAL("Error", msg.str().c_str());
    tlm_gp->set_data_length(i_m_length);
  
    p >> i_m_response_status;

    p >> i_m_dmi;

    tlm_gp->set_response_status(tlm_response_status(i_m_response_status));
  
    p >> i_m_byte_enable_length;
    if (i_m_byte_enable_length)
      i_m_byte_enable = new unsigned char [i_m_byte_enable_length];
    for (unsigned j = 0; j < i_m_byte_enable_length; j++)
      p >> i_m_byte_enable[j];
    tlm_gp->set_byte_enable_ptr(i_m_byte_enable);
  
    p >> i_m_byte_enable_length;
    tlm_gp->set_byte_enable_length(i_m_byte_enable_length);
  
    p >> i_m_streaming_width;
    tlm_gp->set_streaming_width(i_m_streaming_width);
  
    p >> i_extensions_size;
  
    i_extension = 0;
  
    for (unsigned int j = 0; j < i_extensions_size; j++) {
      p >> i_extension;
      if (i_extension) {
        unsigned int id = ml_tlm2_class_company::get_ext_companion(typeid(*i_extension))->get_ext_id(i_extension);
        tlm_gp->set_auto_extension(id, i_extension);
      }
    }
}

void ml_tlm2_gp_companion::clear(const type_info & actual_type, tlm_generic_payload * tlm_gp)
{
  tlm_gp->free_all_extensions();
  if (tlm_gp->get_data_ptr()) {
    delete [] tlm_gp->get_data_ptr();
    tlm_gp->set_data_ptr(NULL);
  }
  if (tlm_gp->get_byte_enable_ptr()) {
    delete [] tlm_gp->get_byte_enable_ptr();
    tlm_gp->set_byte_enable_ptr(NULL);
  }
  uvm_ml_class_companion * comp = uvm_ml_class_company::get_companion(actual_type);
  if (comp == NULL) {
    string err_str = "Class with type_info.name() " + string(actual_type.name()) + " was not registered via ML_TLM2_GP_BEGIN or ML_TLM2_GP_EXT_BEGIN macro";
    SC_REPORT_FATAL("Error", err_str.c_str());
    return;
  }
  comp->uvm_ml_automation(NULL, tlm_gp, NULL, ML_TLM2_DELETE_OP);
}

void  ml_tlm2_connector_base::register_top_of_the_socket_name(const string & sname) {
  if ((IN_ELABORATION() == false) && (uvm_ml_utils::quasi_static_elaboration_started() == false)) {
    // Need to register the static SystemC socket path at the backplane
    size_t posDelim = sname.find_first_of(".");
    string path_top;
    if (posDelim != string::npos)
      path_top = sname.substr(0, posDelim);
    else
      path_top = sname; // should be an error

    uvm_ml_utils::register_static_top(path_top);
  }
}

}
