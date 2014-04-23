//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
//   Copyright 2012-2013 Advanced Micro Devices Inc.
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

//------------------------------------------------------------------------------
/*! @file uvm_ml_adapter.cpp
 *
 *  @brief Adapter header implementing the required API.
 */
#define SC_INCLUDE_DYNAMIC_PROCESSES

#include "uvm_ml_adapter_imp_spec_headers.h"
#include "uvm_ml_adapter_imp_spec_macros.h"
#define SC_INCLUDE_DYNAMIC_PROCESSES

#include "systemc.h"

#include <algorithm>
#include "bp_provided.h"


#include "common/uvm_ml_adapter.h"
#include "common/ml_tlm2/ml_tlm2_connector.h"
#include "common/uvm_ml_hierarchy.h"
#include "common/uvm_ml_phase.h"
#include "common/uvm_ml_config_rsrc.h"
#include "uvm_imp_spec_macros.h"

#include "base/uvm_factory.h"
#include "base/uvm_packer.h"
#include "base/uvm_component.h"
#include "base/uvm_phase.h"
#include "base/uvm_common_schedule.h"
#include "base/uvm_ids.h"

#include "uvm_ml_packer.h"

#include <queue>
#include <map>
#include <dlfcn.h>

using namespace std;

using namespace sc_core;
using namespace uvm;
// FIXME
extern void uvm_ml_notify_end_of_quasi_static_elab();

uvm_ml_packed_obj::uvm_ml_packed_obj() :
  size(0), val(0), max_words(0) {
}

uvm_ml_packed_obj::~uvm_ml_packed_obj() {
  if (val) {
    delete[] val;
  }
}

void uvm_ml_packed_obj::allocate(uvm_ml_packed_obj* v, unsigned nwords) {
  if (v->max_words >= nwords)
    return;
  // need to allocate new m/m
  v->max_words = nwords;
  if (v->val) {
    delete[] v->val;
  }
  v->val = new unsigned[v->max_words];
}

///////////////////////

namespace uvm_ml {



//------------------------------------------------------------------------------
//! Function: report_sc_error
/*! uvm_ml-oriented wrapper for sc_error.
 *
 *  @param message - the main message
 *  @param submessage - submessage
 *
 *  @returns: 
 *   void
 */
void uvm_ml_utils::report_sc_error(const char * const message, const char * const submessage) {
    UVM_ML_SC_REPORT_ERROR(message, submessage);
}

void uvm_ml_utils::print_sc_report(const sc_report& ex) {
    UVM_ML_SC_PRINT_REPORT(ex);
}

static unsigned top_component_id = 0;

static unsigned framework_id = INITIALIZE_FRAMEWORK_IF_NEEDED();


//------------------------------------------------------------------------------
//! ML interface for the SC adaptor.
//
class uvm_ml_tlm_rec {
public:
  static int  startup();
  static void sim_bootstrap();
  static int  construct_top(const char* top_identifier, const char * instance_name);

  static void        set_debug_mode(int mode);
  static void        set_packing_mode(int mode);
  static int         find_connector_id_by_name(const char * path); 
  static const char* get_connector_intf_name(unsigned connector_id); 
  static char*       get_connector_REQ_name(unsigned connector_id); 
  static char*       get_connector_RSP_name(unsigned connector_id); 
  static unsigned    is_export_connector(unsigned connector_id); 
  static int         set_multiport(char* port_name);
  
  #include "uvm_ml_tlm_rec_imp_spec.h"

  static int get(
    unsigned           connector_id, 
    unsigned*          stream_size_ptr,
    uvm_ml_stream_t    stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
  );
  static uvm_ml_tlm_transrec_base* get_transrec_base(
    unsigned connector_id
  );
  static uvm_ml_tlm_receiver_base* get_receiver_base(
    unsigned connector_id
  );
  static uvm_ml_tlm_transmitter_base* get_transmitter_base(
    unsigned connector_id
  );

  static int put(
    unsigned connector_id, 
    unsigned stream_size, 
    uvm_ml_stream_t stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
  );
  static int request_put(
    unsigned connector_id, 
    unsigned call_id, 
    unsigned callback_adapter_id, 
    unsigned stream_size, 
    uvm_ml_stream_t stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static int nb_put(
    unsigned         connector_id, 
    unsigned         stream_size , 
    uvm_ml_stream_t  stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static int can_put(
    unsigned connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static int request_get(
    unsigned connector_id, 
    unsigned call_id,
    unsigned callback_adapter_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static unsigned get_requested(
    unsigned connector_id, 
    unsigned call_id , 
    uvm_ml_stream_t stream 
  ); 
  static int nb_get(
    unsigned connector_id, 
    unsigned * stream_size_ptr,
    uvm_ml_stream_t stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static int can_get(
    unsigned         connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  );
  static int peek(
  unsigned connector_id, 
  unsigned* stream_size_ptr,
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit * time_unit, 
  double           * time_value
  );  
  static int request_peek(
    unsigned connector_id, 
    unsigned call_id,
    unsigned callback_adapter_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static unsigned peek_requested(
    unsigned connector_id,
    unsigned call_id,
    uvm_ml_stream_t stream 
   );

  static int nb_peek(
    unsigned connector_id, 
    unsigned * stream_size_ptr,
    uvm_ml_stream_t stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static int can_peek(
    unsigned connector_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static int transport(
    unsigned connector_id, 
    unsigned req_stream_size, 
    uvm_ml_stream_t req_stream,
    unsigned* rsp_stream_size, 
    uvm_ml_stream_t rsp_stream, 
    uvm_ml_time_unit * time_unit, 
    double           * time_value
  );
  static int request_transport(
    unsigned connector_id, 
    unsigned call_id, 
    unsigned callback_adapter_id, 
    unsigned req_stream_size, 
    uvm_ml_stream_t req_stream,
    unsigned* rsp_stream_size, 
    uvm_ml_stream_t rsp_stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 
  static unsigned transport_response(
    unsigned            connector_id,
    unsigned            call_id,
    uvm_ml_stream_t rsp_stream
  );
  static int nb_transport(
    unsigned connector_id, 
    unsigned req_stream_size, 
    uvm_ml_stream_t req_stream,
    unsigned* rsp_stream_size, 
    uvm_ml_stream_t rsp_stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  );
  static void write(
    unsigned connector_id, 
    unsigned stream_size , 
    uvm_ml_stream_t stream, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  ); 

  static void notify_end_blocking(
    unsigned call_id, 
    uvm_ml_time_unit time_unit, 
    double           time_value
  );

  // TLM2
  static int tlm2_b_transport(
    unsigned              connector_id, 
    unsigned *            stream_size_ptr,
    uvm_ml_stream_t * stream_ptr,
    uvm_ml_time_unit *    delay_unit,
    double *              delay_value, 
    uvm_ml_time_unit      time_unit, 
    double                time_value
  );

  static int tlm2_b_transport_request(
    unsigned              connector_id, 
    unsigned              call_id,
    unsigned              callback_adapter_id,
    unsigned              stream_size,
    uvm_ml_stream_t   stream,
    uvm_ml_time_unit      delay_unit,
    double                delay_value, 
    uvm_ml_time_unit      time_unit, 
    double                time_value
  );

  static void tlm2_transport_request_helper(
    ml_tlm2_target_connector_base * conn,
    unsigned                        call_id,
    unsigned                        callback_adapter_id,
    MLUPO*                          mlupo_req_stream,
    sc_time_unit                    delay_unit, 
    double                          delay_value, 
    sc_time_unit                    time_unit, 
    double                          time_value
  );

  static int tlm2_b_transport_response(
    unsigned              connector_id, 
    unsigned              call_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream
  );

  static uvm_ml_tlm_sync_enum tlm2_nb_transport_fw(
    unsigned              connector_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream,
    uvm_ml_tlm_phase *   phase,
    unsigned int          transaction_id,
    uvm_ml_time_unit *    delay_unit,
    double *              delay_value, 
    uvm_ml_time_unit      time_unit, 
    double                time_value
  );

  static uvm_ml_tlm_sync_enum tlm2_nb_transport_bw(
    unsigned              connector_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream,
    uvm_ml_tlm_phase *   phase,
    unsigned int          transaction_id,
    uvm_ml_time_unit *    delay_unit,
    double *              delay_value, 
    uvm_ml_time_unit      time_unit, 
    double                time_value  
  );

  static unsigned tlm2_transport_dbg(
    unsigned              connector_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream, 
    uvm_ml_time_unit      time_unit, 
    double                time_value
  );

  static void tlm2_turn_off_transaction_mapping(const char* socket_name);

  static void synchronize(
    uvm_ml_time_unit      time_unit, 
    double                time_value
  );

  static int create_child_junction_node(
    const char * component_type_name,
    const char * instance_name,
    const char * parent_full_name,
    int          parent_framework_id,
    int          parent_junction_node_id
  );

}; // class uvm_ml_tlm_rec

vector<sc_module *> uvm_ml_utils::quasi_static_tree_nodes;
vector<string> uvm_ml_utils::static_top_names;

static bp_frmw_c_api_struct* uvm_ml_sc_get_required_api()
{
    bp_frmw_c_api_struct * required_api = new bp_frmw_c_api_struct();
    memset(required_api, '\0', sizeof(bp_frmw_c_api_struct));
    required_api->set_trace_mode_ptr= uvm_ml_tlm_rec::set_debug_mode;
    required_api->startup_ptr = uvm_ml_tlm_rec::startup;
    required_api->construct_top_ptr=uvm_ml_tlm_rec::construct_top;

    // ----- Phasing APIs
    required_api->transmit_phase_ptr = uvm_ml_phase::transmit_phase;
    required_api->notify_phase_ptr = uvm_ml_phase::notify_phase;
    required_api->notify_runtime_phase_ptr = uvm_ml_phase::notify_runtime_phase;

    required_api->find_connector_id_by_name_ptr = uvm_ml_tlm_rec::find_connector_id_by_name;
    required_api->get_connector_intf_name_ptr = uvm_ml_tlm_rec::get_connector_intf_name;
    required_api->is_export_connector_ptr = uvm_ml_tlm_rec::is_export_connector;
    required_api->try_put_uvm_ml_stream_ptr = uvm_ml_tlm_rec::nb_put;
    required_api->can_put_ptr = uvm_ml_tlm_rec::can_put;
    required_api->put_uvm_ml_stream_request_ptr = uvm_ml_tlm_rec::request_put;
    required_api->get_uvm_ml_stream_request_ptr = uvm_ml_tlm_rec::request_get;
    required_api->get_requested_uvm_ml_stream_ptr = uvm_ml_tlm_rec::get_requested;
    required_api->try_get_uvm_ml_stream_ptr = uvm_ml_tlm_rec::nb_get;
    required_api->can_get_ptr = uvm_ml_tlm_rec::can_get;
    required_api->peek_uvm_ml_stream_request_ptr = uvm_ml_tlm_rec::request_peek;
    required_api->peek_requested_uvm_ml_stream_ptr = uvm_ml_tlm_rec::peek_requested;
    required_api->try_peek_uvm_ml_stream_ptr = uvm_ml_tlm_rec::nb_peek;
    required_api->can_peek_ptr = uvm_ml_tlm_rec::can_peek;
    required_api->transport_uvm_ml_stream_request_ptr = uvm_ml_tlm_rec::request_transport;
    required_api->transport_response_uvm_ml_stream_ptr = uvm_ml_tlm_rec::transport_response;
    required_api->nb_transport_uvm_ml_stream_ptr = uvm_ml_tlm_rec::nb_transport;
    required_api->write_uvm_ml_stream_ptr = uvm_ml_tlm_rec::write;
    required_api->notify_end_blocking_ptr = uvm_ml_tlm_rec::notify_end_blocking;
    required_api->tlm2_b_transport_request_ptr = uvm_ml_tlm_rec::tlm2_b_transport_request;
    required_api->tlm2_b_transport_response_ptr = uvm_ml_tlm_rec::tlm2_b_transport_response;
    required_api->tlm2_nb_transport_fw_ptr =  uvm_ml_tlm_rec::tlm2_nb_transport_fw;
    required_api->tlm2_nb_transport_bw_ptr = uvm_ml_tlm_rec::tlm2_nb_transport_bw;
    required_api->tlm2_transport_dbg_ptr = uvm_ml_tlm_rec::tlm2_transport_dbg;
    required_api->tlm2_turn_off_transaction_mapping_ptr = (uvm_ml_tlm_rec::tlm2_turn_off_transaction_mapping);
    required_api->synchronize_ptr = uvm_ml_tlm_rec::synchronize;

    required_api->create_child_junction_node_ptr = uvm_ml_tlm_rec::create_child_junction_node;

    required_api->notify_config_ptr = uvm_ml_config_rsrc::notify_config;
    required_api->notify_resource_ptr = uvm_ml_config_rsrc::notify_resource;

    return required_api;
};

#define BP(f) (*bpProvidedAPI->f##_ptr)

static bp_api_struct * bpProvidedAPI = NULL;

//////////////////////
} // namespace uvm_ml


#include "uvm_ml_adapter_imp_spec.cpp"

// this belongs in uvm_ml_hierarchy.cpp
map<uvm_component*,unsigned>proxy_parents;


int unsigned get_hierarchical_node_id(uvm_component *comp) {
  static int unsigned next_id = 0;
  map<uvm_component*, unsigned>::iterator it;
  
  it = proxy_parents.find(comp);
  if(it == proxy_parents.end()) {
    proxy_parents.insert(pair<uvm_component*,unsigned>(comp,next_id++));
    return next_id-1;
  } else
    return it->second;

} // get_hierarchical_node_id

child_component_proxy::child_component_proxy(sc_module_name nm): uvm_ml_special_component(nm) {

    //get_config_string("uvm_ml_parent_name", m_parent_name);
    //get_config_string("uvm_ml_type_name",   m_component_type_name);
    //get_config_string("uvm_ml_inst_name",   m_instance_name);
    //get_config_string("uvm_ml_frmw_id",     m_target_frmw_ind);

    uvm_get_config_string("uvm_ml_parent_name", m_parent_name);
    uvm_get_config_string("uvm_ml_type_name",   m_component_type_name);
    uvm_get_config_string("uvm_ml_inst_name",   m_instance_name);
    uvm_get_config_string("uvm_ml_frmw_id",     m_target_frmw_ind);

    uvm_component *p = get_parent();
    m_parent_id = get_hierarchical_node_id(p);

    m_child_junction_node_id = BP(create_child_junction_node)(framework_id,
				                              m_target_frmw_ind.c_str(), 
				                              m_component_type_name.c_str(),
				                              m_instance_name.c_str(),
				                              m_parent_name.c_str(),
				                              m_parent_id);
    if(m_child_junction_node_id == -1) {
      char msg[1024];
      sprintf(msg,"\ntype name is %s; instance name is %s; framework is %s", m_component_type_name.c_str(), m_instance_name.c_str(), m_target_frmw_ind.c_str());
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: Failed to create child proxy", msg);
    }
}

void child_component_proxy::phase_started(uvm_phase *phase) { 
    char * phase_name  = const_cast<char*>(phase->get_name().c_str());
    char * phase_group = const_cast<char*>(phase->get_schedule()->basename());

  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, phase_group, phase_name, UVM_ML_PHASE_STARTED);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: phase_started failed, framework does not exist", "");
  }
}

void child_component_proxy::phase_ready_to_end(uvm_phase *phase) { 
    char * phase_name  = const_cast<char*>(phase->get_name().c_str());
    char * phase_group = const_cast<char*>(phase->get_schedule()->basename());

  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, phase_group, phase_name, UVM_ML_PHASE_READY_TO_END);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: phase_ready_to_end failed, framework does not exist", "");
  }
}

void child_component_proxy::phase_ended(uvm_phase *phase) { 
    char * phase_name  = const_cast<char*>(phase->get_name().c_str());
    char * phase_group = const_cast<char*>(phase->get_schedule()->basename());

  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, phase_group, phase_name, UVM_ML_PHASE_ENDED);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: phase_ended failed, framework does not exist", "");
  }
}

void child_component_proxy::build_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "build", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: build_phase failed, framework does not exist", "");
  }
}
void child_component_proxy::connect_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "connect", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: connect_phase failed, framework does not exist", "");
  }
}
void child_component_proxy::end_of_elaboration_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "end_of_elaboration", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: end_of_elaboration_phase failed, framework does not exist", "");
  }
}
void child_component_proxy::start_of_simulation_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "start_of_simulation", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: start_of_simulation_phase failed, framework does not exist", "");
  }
}

void child_component_proxy::extract_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "extract", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: extract_phase failed, framework does not exist", "");
  }
}

void child_component_proxy::check_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "check", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: check_phase failed, framework does not exist", "");
  }
}

void child_component_proxy::report_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "report", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: report_phase failed, framework does not exist", "");
  }
}

void child_component_proxy::final_phase(uvm_phase *phase) { 
  int res = BP(transmit_phase)(framework_id, m_target_frmw_ind.c_str(), m_child_junction_node_id, "common", "final", UVM_ML_PHASE_EXECUTING);
  if(res == 0) {
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: final_phase failed, framework does not exist", "");
  }
}

///////////////////////

namespace uvm_ml {


void report_tlm1_error(uvm_ml_tlm_receiver_base* rec) {
  char msg[1024];
  if (rec) {
    sprintf(msg, "\nSystemC export name is '%s'\n"
            "TLM1 interface is '%s'\n"
            "uvm_object payload type is '%s'\n", 
            rec->object()->name(), 
            rec->get_intf_name().c_str(), 
            rec->get_REQ_name().c_str()
           );
    SC_REPORT_WARNING(ML_UVM_RUN_TIME_ERROR_, msg);
  } else {
    SC_REPORT_WARNING(ML_UVM_RUN_TIME_ERROR_, "\n");
  }
  CURRENT_SIMCONTEXT_SET_ERROR();
}

void report_connector_error(ml_tlm2_connector_base* conn) {
  char msg[1024];
  if (conn) {
    sprintf(msg, "\nTLM2 connector\n");
    SC_REPORT_WARNING(ML_UVM_RUN_TIME_ERROR_, msg);
  } else {
    SC_REPORT_WARNING(ML_UVM_RUN_TIME_ERROR_, "\n");
  }
  CURRENT_SIMCONTEXT_SET_ERROR();
}

} // namespace uvm_ml


///////////////////////

namespace uvm_ml {


uvm_ml_tlm_conn_info::uvm_ml_tlm_conn_info(string name, unsigned id) {
  m_name = name;
  m_id = id;
  m_object = sc_find_object(name.c_str());
  if (!m_object) {
    char msg[1024];
    sprintf(msg, "\nPort/export is '%s' \n", name.c_str());
    SC_REPORT_ERROR(ML_UVM_OBJ_NOT_FOUND_, msg);
    return;
  }
}

unsigned uvm_ml_utils::m_nextid = 1;   

bool uvm_ml_utils::m_quasi_static_elaboration_started = false;

bool uvm_ml_utils::m_quasi_static_end_of_construction = false;

sc_strhash<uvm_ml_tlm_conn_info*>* uvm_ml_utils::conn_info_by_name = 0;

map<unsigned,uvm_ml_tlm_conn_info*>* uvm_ml_utils::conn_info_by_id = 0;

map<sc_object*, uvm_ml_tlm_transrec_base*>* uvm_ml_utils::obj_transrec_map = 0;

map<std::string, unsigned>* uvm_ml_utils::socket_map = 0;

map<unsigned, ml_tlm2_connector_base*>* uvm_ml_utils::connector_map = 0;


void uvm_ml_utils::add_socket(string s, ml_tlm2_connector_base* conn) {
  pair<map<string,unsigned>::iterator,bool> ret_soc; 
  pair<map<unsigned, ml_tlm2_connector_base*>::iterator,bool> ret_conn; 

  if (!socket_map) {
    socket_map = new map<std::string, unsigned>();
  }
  conn->conn_id = m_nextid++;
  ret_soc = socket_map->insert(pair<string,unsigned>(s,conn->conn_id));
  if (!connector_map) {
    connector_map = new map<unsigned, ml_tlm2_connector_base*>();
  }
  ret_conn = connector_map->insert(pair<unsigned,ml_tlm2_connector_base*>(conn->conn_id,conn));
  //connector_map[m_nextid-1] = conn;
}

ml_tlm2_connector_base* uvm_ml_utils::get_ml_tlm2_connector_base(unsigned target_connector_id)
  {
    map<unsigned, ml_tlm2_connector_base*>::iterator it;

    it = connector_map->find(target_connector_id);
    if (it == connector_map->end()) return 0;
    return connector_map->find(target_connector_id)->second;
  }

unsigned uvm_ml_utils::find_socket_id(string s) {
  if (socket_map == NULL) return 0;

  map<string,unsigned>::iterator it;
  it = socket_map->find(s);
  if (it == socket_map->end()) return 0;
  return socket_map->find(s)->second;
}

bool uvm_ml_utils::is_tlm2_connector(unsigned connector_id) {
  if (uvm_ml_utils::connector_map == NULL) return false;

  map<unsigned, ml_tlm2_connector_base*>::iterator it;

  it = uvm_ml_utils::connector_map->find(connector_id);
  if (it == uvm_ml_utils::connector_map->end()) 
    return false;
  else
    return true;
}

void uvm_ml_utils::add_transrec_to_map(
  sc_object* obj, 
  uvm_ml_tlm_transrec_base* tr
) {
  if (!obj_transrec_map) {
    obj_transrec_map = new map<sc_object*, uvm_ml_tlm_transrec_base*>();
  }
  (*obj_transrec_map)[obj] = tr;
}

uvm_ml_tlm_transrec_base* uvm_ml_utils::get_transrec(sc_object* obj) {
  if (!obj_transrec_map) return 0;
  return (*obj_transrec_map)[obj];
}

uvm_ml_tlm_conn_info* uvm_ml_utils::get_or_create_conn_info(string name) {
  if (!conn_info_by_name) {
    conn_info_by_name = new sc_strhash<uvm_ml_tlm_conn_info*>();
  }
  if (!conn_info_by_id) {
    conn_info_by_id = new map<unsigned,uvm_ml_tlm_conn_info*>();
  }
  uvm_ml_tlm_conn_info* info = get_conn_info(name);
  if (!info) {
    unsigned id = m_nextid++;
    info = new uvm_ml_tlm_conn_info(name,id);
  }
  (*conn_info_by_id)[info->id()] = info;
  conn_info_by_name->insert(strdup(name.c_str()),info);
  return info;
}

uvm_ml_tlm_conn_info* uvm_ml_utils::get_conn_info(string name) {
  std::string s;
  s = name;
  if (!conn_info_by_name) return 0;
  return (*conn_info_by_name)[s.c_str()];
}

uvm_ml_tlm_conn_info* uvm_ml_utils::get_conn_info(unsigned id) {
  if (!conn_info_by_id) return 0;
  return (*conn_info_by_id)[id];
}

///////////////////////

static unsigned fake_blocking_call_id;

static sc_phash<void*, sc_event*> call_id_trans_dict;

static sc_phash<void*, uvm_ml_packed_obj*> call_id_rec_dict;

// Save delay values for fake blocking
static map<unsigned, sc_time_unit> call_id_delay_unit_dict;
static map<unsigned, double> call_id_delay_value_dict;

unsigned uvm_ml_utils::FrameworkId() { 
  return framework_id; 
}

unsigned uvm_ml_utils::uvm_ml_tlm_id_from_name(std::string name) {
  uvm_ml_tlm_conn_info* info = get_conn_info(name);
  if (!info) return unsigned(-1);
  return info->id();
}

bool uvm_ml_utils::is_tree_node_quasi_static(unsigned root_node_id)
{
  return root_node_id >= static_top_names.size();
}

sc_module * uvm_ml_utils::get_quasi_static_tree_node_by_id(unsigned node_id)
{
 char msg[1024];
  if(!((node_id >= static_top_names.size()) && (node_id < static_top_names.size() + quasi_static_tree_nodes.size()))) {
    sprintf(msg,"\nID is %d", node_id);
    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: Subtree node was not found",msg);
    return NULL;
  };
  //assert ((node_id >= static_top_names.size()) && (node_id < static_top_names.size() + quasi_static_tree_nodes.size())); // Otherwise an internal error
  return quasi_static_tree_nodes[node_id - static_top_names.size()];
}

// TLM2
static uvm_ml_time_unit m_time_unit = TIME_UNIT_UNDEFINED;
static double           m_time_value = -1;

unsigned int uvm_ml_tlm_trans::tlm2_nb_transport_bw(
      unsigned         connector_id,
      MLUPO *          val,
      unsigned int *   phase,
      unsigned int     transaction_id,
      sc_time_unit *   delay_unit,
      double *         delay_value
) {
  unsigned int ret;
  unsigned *ptr;

  ptr = val->val; // save pointer
  ret = (unsigned int) BP(nb_transport_bw)(
				      framework_id,
				      connector_id,
				      &(val->size),
				      &(val->val),
				      (uvm_ml_tlm_phase *)phase,
                                      transaction_id,
				      (uvm_ml_time_unit *) delay_unit,
				      delay_value,
                                      m_time_unit,
                                      m_time_value
				      );
  if(val->val != ptr) delete[] ptr; // delete old value if it was reassigned
  return ret;
}

unsigned int uvm_ml_tlm_trans::tlm2_nb_transport_fw(
      unsigned         connector_id,
      MLUPO *          val,
      unsigned int *   phase,
      unsigned int     transaction_id,
      sc_time_unit *   delay_unit,
      double *         delay_value 
) {
  unsigned int ret;
  unsigned *ptr;

  ptr = val->val; // save pointer
  ret = (unsigned int) BP(nb_transport_fw)(
				      framework_id,
				      connector_id,
				      &(val->size),
				      &(val->val),
				      (uvm_ml_tlm_phase *)phase,
                                      transaction_id,
				      (uvm_ml_time_unit *) delay_unit,
				      delay_value, 
                                      m_time_unit,
                                      m_time_value
				      );
  if(val->val != ptr) delete[] ptr; // delete old value if it was reassigned
  return ret;
}

unsigned uvm_ml_tlm_trans::tlm2_transport_dbg(
      unsigned              connector_id,
      MLUPO *               val 
) {
  unsigned int ret;
  unsigned *ptr;

  ptr = val->val; // save pointer
  ret = BP(transport_dbg)(
				      framework_id,
				      connector_id,
				      &(val->size),
				      &(val->val),
                                      m_time_unit,
                                      m_time_value
				      );
  if(val->val != ptr) delete[] ptr; // delete old value if it was reassigned
  return ret;
}

void uvm_ml_tlm_trans::tlm2_b_transport(
      unsigned         connector_id,
      MLUPO *          val,
      sc_time_unit *   delay_unit,
      double *         delay_value
) {
  unsigned *ptr;
  unsigned call_id = fake_blocking_call_id++;
  unsigned done = 0;

  ptr = val->val; // save pointer
  int disable = BP(request_b_transport_tlm2)(
				      framework_id,
				      connector_id,
				      call_id,
				      &(val->size),
				      &(val->val),
				      (uvm_ml_time_unit)*delay_unit,
				      *delay_value,
                                      &done,
                                      m_time_unit,
                                      m_time_value
				      );
  if(val->val != ptr) delete[] ptr; // delete old value if it was reassigned

  if (!done) {
    // new sc_event; hash <call_id , event>; wait on event;
    // later target will cause event to be triggered
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void *)(unsigned long)call_id;

    sc_event* e = new INVISIBLE_EVENT("uvm_fake_blocking");

    call_id_trans_dict.insert(p_call_id, e);
    sc_core::wait(*e);
    // we are here when the target framework has informed us via 
    // the backplane that the call has finished in it;
    // get the return value of get() from the backplane
    ptr = val->val; // save pointer
    int ret =  BP(b_transport_tlm2_response)(
				      framework_id,
				      connector_id,
				      call_id,
				      &(val->size),
				      val->val
				      );
    if(val->val != ptr) delete[] ptr; // delete old value if it was reassigned
    delete e;
  }

  if (disable == 1) {

      uvm_ml::dpi_task_disabled();
  }
}

// Return -1 for failure
int uvm_ml_tlm_rec::construct_top(const char* top_identifier, const char * instance_name) {
 char msg[1024];
 try {
     sc_module * m = NULL;
     // first see if object can be created by uvm factory
     if (uvm_factory::is_component_registered(std::string(top_identifier))) {
       m = uvm_factory::create_component(std::string(top_identifier), "", 
                                         std::string(instance_name));
       // assuming nothing can go wrong in creation
       //assert(m);
       if(m == NULL) {
	 sprintf(msg,"\ntop identifier is %s; instance name is %s\n", top_identifier, instance_name);
	 UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: top component could not be created",msg);
	 return -1;
       };
     } else {
       // not uvm_component registered with factory
       // see if it is sc_module
       m = QUASI_STATIC_CONSTRUCT_TOP(std::string(top_identifier), std::string(instance_name));

       if (!m) {
         // not module, now print error that not registered with factory
         char msg[1024];
         sprintf(msg, "\nSystemC object name is '%s'", top_identifier); 
         cerr << "before thorowing error"<< endl;
         SC_REPORT_ERROR(ML_UVM_MISSING_REGISTRATION_, msg);
         return -1;
       }
    }
    return uvm_ml_utils::add_quasi_static_tree_node(m);
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}


void uvm_ml_tlm_rec::set_debug_mode(int mode) {
}

void uvm_ml_tlm_rec::set_packing_mode(int mode) {
}

int uvm_ml_tlm_rec::find_connector_id_by_name(const char * path) { 
  try {
    unsigned conn_id = uvm_ml_utils::find_socket_id(path);
    if (conn_id != 0) {
      return conn_id;
    }
    sc_object* obj = sc_find_object(path);
    if (!obj) {
      char msg[1024];
      sprintf(msg, "\nPort/export is '%s' \n", path);
      SC_REPORT_ERROR(ML_UVM_OBJ_NOT_FOUND_, msg);
      return 0;
    }
    uvm_ml_tlm_transrec_base* tr = uvm_ml_utils::get_transrec(obj);
    if (!tr) {
      char msg[1024];
      sprintf(msg, "\nPort/export is '%s' \n", path);
      SC_REPORT_ERROR(ML_UVM_NO_TRANS_REC_, msg);
      return 0;
    }
    tr->id_is_valid(true);
    uvm_ml_tlm_conn_info* info =
      uvm_ml_utils::get_or_create_conn_info(path);
    return info->id();
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

static std::string map_intf_name(std::string s) {
  try {
    if (s=="tlm_blocking_put_if") return "tlm_blocking_put";
    if (s=="tlm_nonblocking_put_if") return "tlm_nonblocking_put";
    if (s=="tlm_put_if") return "tlm_put";
  
    if (s=="tlm_blocking_get_if") return "tlm_blocking_get";
    if (s=="tlm_nonblocking_get_if") return "tlm_nonblocking_get";
    if (s=="tlm_get_if") return "tlm_get";

    if (s=="tlm_blocking_peek_if") return "tlm_blocking_peek";
    if (s=="tlm_nonblocking_peek_if") return "tlm_nonblocking_peek";
    if (s=="tlm_peek_if") return "tlm_peek";

    if (s=="tlm_blocking_get_peek_if") return "tlm_blocking_get_peek";
    if (s=="tlm_nonblocking_get_peek_if") return "tlm_nonblocking_get_peek";
    if (s=="tlm_get_peek_if") return "tlm_get_peek";

    if (s=="tlm_master_if") return "tlm_master";
    if (s=="tlm_slave_if") return "tlm_slave";

    if (s=="tlm_transport_if") return "tlm_blocking_transport";
    if (s=="tlm_analysis_if") return "tlm_analysis";
    return s;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, s, 0, 0)
}

const char* uvm_ml_tlm_rec::get_connector_intf_name(
  unsigned connector_id
) { 
  try {
    if(uvm_ml_utils::is_tlm2_connector(connector_id)) {
      char* e = (char*)("TLM2");
      return e;
    }
    static std::string sm;
    uvm_ml_tlm_transrec_base* tr = get_transrec_base(connector_id);
    if (!tr) {
      char* e = (char*)("ERROR");
      return e;
    }
    std::string s = tr->get_intf_name();
    sm = map_intf_name(s);
    char* c = (char*)(sm.c_str());
    return c;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

char* uvm_ml_tlm_rec::get_connector_REQ_name(
  unsigned connector_id
) { 
  try {
    static std::string sm;
    if(uvm_ml_utils::is_tlm2_connector(connector_id)) {
      char* c = (char*)(sm.c_str());
      return c;
    }
    uvm_ml_tlm_transrec_base* tr = get_transrec_base(connector_id);
    if (!tr) {
      char* e = (char*)("ERROR");
      return e;
    }
    sm = tr->get_REQ_name();
    char* c = (char*)(sm.c_str());
    return c;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

char* uvm_ml_tlm_rec::get_connector_RSP_name(
  unsigned connector_id
) { 
  try {
    static std::string sm;
    if(uvm_ml_utils::is_tlm2_connector(connector_id)) {
      char* c = (char*)(sm.c_str());
      return c;
    }
    uvm_ml_tlm_transrec_base* tr = get_transrec_base(connector_id);
    if (!tr) {
      char* e = (char*)("ERROR");
      return e;
    }
    sm = tr->get_RSP_name();
    char* c = (char*)(sm.c_str());
    return c;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

unsigned uvm_ml_tlm_rec::is_export_connector(
  unsigned connector_id
) { 
  try {
    if(uvm_ml_utils::is_tlm2_connector(connector_id)) {
      ml_tlm2_connector_base* conn = uvm_ml_utils::get_ml_tlm2_connector_base(connector_id);
      return conn->is_target;
    }
    uvm_ml_tlm_conn_info* info = 
      uvm_ml_utils::get_conn_info(connector_id);
    if (!info) {
      SC_REPORT_ERROR(UVM_CONNECTOR_ID_NOT_FOUND_,"");
      return 0;
    }
    sc_object* obj = info->object();
    uvm_ml_tlm_transrec_base* tr = uvm_ml_utils::get_transrec(obj);
    if (!tr) {
      char msg[1024];
      sprintf(msg, "\nPort/export is '%s' \n", obj->name());
      SC_REPORT_ERROR(ML_UVM_NO_TRANS_REC_, msg);
      return 0;
    }
    if (tr->is_transmitter()) {
      return 0;
    }
    return 1;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

int uvm_ml_tlm_rec::set_multiport(char* port_name) {
  try {
    // multiport, error out
    char msg[1024];
    sprintf(msg, "\nPort is '%s' \n", port_name);
    SC_REPORT_ERROR(ML_UVM_NO_MULTIPORT_, msg);
    return 0;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

uvm_ml_tlm_transrec_base* uvm_ml_tlm_rec::get_transrec_base(
  unsigned connector_id
) {
  try {
    uvm_ml_tlm_conn_info* info = uvm_ml_utils::get_conn_info(connector_id);
    sc_object* obj = info->object();
    uvm_ml_tlm_transrec_base* tr = uvm_ml_utils::get_transrec(obj);
    if (!tr) {
      // should this really be an assert that tr exists? Should not have come 
      // this far otherwise
      char msg[1024];
      sprintf(msg, "\nPort/export is '%s' \n", obj->name());
      SC_REPORT_ERROR(ML_UVM_NO_TRANS_REC_, msg);
    }
    return tr;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

uvm_ml_tlm_receiver_base* uvm_ml_tlm_rec::get_receiver_base(
  unsigned connector_id
) {
  try {
    uvm_ml_tlm_transrec_base* tr = get_transrec_base(connector_id);
    if (!tr) return 0;
    if (tr->is_transmitter()) {
      SC_REPORT_ERROR(UVM_RECEIVER_NOT_VALID_,"");
      return 0;
    }
    uvm_ml_tlm_receiver_base* rec = DCAST<uvm_ml_tlm_receiver_base*>(tr);
    if (!rec) {
      SC_REPORT_ERROR(UVM_RECEIVER_NOT_VALID_,"");
      return 0;
    }
    return rec;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

uvm_ml_tlm_transmitter_base* uvm_ml_tlm_rec::get_transmitter_base(
  unsigned connector_id
) {
  try {
    // never called
    uvm_ml_tlm_transrec_base* tr = get_transrec_base(connector_id);
    if (!tr) return 0;
    if (!(tr->is_transmitter())) {
      SC_REPORT_ERROR(UVM_TRANSMITTER_NOT_VALID_,"");
      return 0;
    }
    uvm_ml_tlm_transmitter_base* trans = DCAST<uvm_ml_tlm_transmitter_base*>(tr);
    if (!trans) {
      SC_REPORT_ERROR(UVM_TRANSMITTER_NOT_VALID_,"");
      return 0;
    }
    return trans;
  }
  UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(UVM_ML_QUASI_STATIC_ELABORATION, 0, 0, 0)
}

// put takes part in disable protocol as it is blocking,
// so exception catching is more specialized
int uvm_ml_tlm_rec::put(
    unsigned connector_id, 
    unsigned stream_size, 
    uvm_ml_stream_t stream, 
  uvm_ml_time_unit * time_unit, 
  double           * time_value
) {
    ENTER_CO_SIMULATION_CONTEXT2();
  int ret = 0;
  EXCEPTION_HANDLER_STORAGE();
  char msg[1024];
  sprintf(msg, "\nTLM function is put");
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      STORE_OLD_EXCEPTION_HANDLER();
    rec = get_receiver_base(connector_id);
    if (!rec) {
        RESTORE_OLD_EXCEPTION_HANDLER();
        EXIT_CO_SIMULATION_CONTEXT();
      return 0;
    }
    ret = rec->put_bitstream(stream_size, stream);
    RESTORE_OLD_EXCEPTION_HANDLER();
    EXIT_CO_SIMULATION_CONTEXT();
    return ret;
  }
  //CATCH_EXCEPTION_POP(msg);
  SC_KILL_CATCHER()
  catch( const sc_report& ex ) {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_PRINT_REPORT(ex);
    report_tlm1_error(rec);

    return ret;

  }
  catch( const ::std::exception& x )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_REPORT_COMPOSE_MESSAGE(x);
      report_tlm1_error(rec);
      return ret;
  }
  catch( const char* s )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
    cout << "\n" << s << "\n";
    report_tlm1_error(rec);
    return ret;
  }
  EXIT_CO_SIMULATION_CONTEXT();
  return ret;

}

void put_bitstream_request_helper(
  uvm_ml_tlm_receiver_base* rec,
  unsigned call_id,
  unsigned callback_adapter_id,
  uvm_ml_packed_obj* mlupo_stream
) {
  try {
    // call blocking put()
    rec->put_bitstream(mlupo_stream->size, mlupo_stream->val);
    // when put() returns, callback into source adapter
    // to inform that call has ended
    uvm_ml_tlm_trans::notify_end_blocking(callback_adapter_id, call_id);
    //delete mlupo_stream;
    uvm_ml_utils::release_mlupo_to_pool(mlupo_stream);
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_3
}

int uvm_ml_tlm_rec::request_put(
  unsigned connector_id, 
  unsigned call_id, 
  unsigned callback_adapter_id, 
  unsigned stream_size, 
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
      rec = get_receiver_base(connector_id);
      if (!rec) { 
          EXIT_CO_SIMULATION_CONTEXT();
          return 0; 
      }
    // this form is called when we're doing fake blocking; so cannot
    // call put() directly and block;
    // instead, spawn a helper thread that will do the blocking call
    // and return
    sc_spawn_options op;

    MARK_THREAD_INVISIBLE(op);
    char name[1024];
    sprintf(name, "put_bitstream_request_helper_%d", call_id);
    
    // copy the stream into a mlupo. This is necessary because it is 
    // likely that in backplane, they use the same stream for 
    // multiple calls - so for back to back calls the arguments will get
    // overwritten until we make a copy here;
    // the helper will delete the mlupo we allocate here when it is done

    //MLUPO* mlupo_stream = new MLUPO;
    MLUPO* mlupo_stream = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::fill_mlupo(*mlupo_stream,stream_size,stream);
  
    sc_core::sc_spawn(sc_bind(&put_bitstream_request_helper,
                              rec,
                              call_id,
                              callback_adapter_id,
                              mlupo_stream
                             ),
                        name, 
                        &op
                     );
    EXIT_CO_SIMULATION_CONTEXT2();
    return 0;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_INT
  return 0;
}

int uvm_ml_tlm_rec::nb_put(
  unsigned connector_id, 
  unsigned stream_size , 
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
      rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    int i = rec->try_put_bitstream(stream_size,stream);
    EXIT_CO_SIMULATION_CONTEXT2();
    return i;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

int uvm_ml_tlm_rec::can_put(
  unsigned connector_id, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    int i = rec->can_put();
    EXIT_CO_SIMULATION_CONTEXT();
    return i;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

// get_bitstream takes part in disable protocol as it is blocking,
// so exception catching is more specialized
int uvm_ml_tlm_rec::get(
  unsigned connector_id, 
  unsigned* stream_size_ptr,
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit * time_unit, 
  double           * time_value
) { 
    ENTER_CO_SIMULATION_CONTEXT2();
  int ret = 0;
  EXCEPTION_HANDLER_STORAGE();
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      STORE_OLD_EXCEPTION_HANDLER();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        RESTORE_OLD_EXCEPTION_HANDLER();
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    ret = rec->get_bitstream(stream_size_ptr, stream);
    RESTORE_OLD_EXCEPTION_HANDLER();
    EXIT_CO_SIMULATION_CONTEXT();
    return ret;
  }
  SC_KILL_CATCHER()
  catch( const sc_report& ex ) {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_PRINT_REPORT(ex);
    report_tlm1_error(rec);
    return ret;
  }
  catch( const ::std::exception& x )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_REPORT_COMPOSE_MESSAGE(x);
      
    report_tlm1_error(rec);
    return ret;
  }
  catch( const char* s )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
    cout << "\n" << s << "\n";
    report_tlm1_error(rec);
    return ret;
  }
  EXIT_CO_SIMULATION_CONTEXT();
  return ret;

}

void get_bitstream_request_helper(
  uvm_ml_tlm_receiver_base* rec,
  unsigned call_id,
  unsigned callback_adapter_id
) {
  try {
    // call blocking get()
    MLUPO* retval = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::allocate_mlupo(retval);
    rec->get_bitstream(&(retval->size), retval->val);
    // when get() returns, first hash return value with call id be 
    // retrieved later thru get_requested_bitstream()
    void* p_call_id;
      // need to do the cast to unsigned long below before casting to pointer
      // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
      // bits; so casting from unsigned to pointer generates compiler warning;
      // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void *)(unsigned long)call_id;
    call_id_rec_dict.insert(p_call_id, retval);
    // callback into source adapter
    // to inform that call has ended
    uvm_ml_tlm_trans::notify_end_blocking(callback_adapter_id, call_id);
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_3
}

int uvm_ml_tlm_rec::request_get(
  unsigned connector_id, 
  unsigned call_id,
  unsigned callback_adapter_id, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) {
        EXIT_CO_SIMULATION_CONTEXT();
      return 0 ;
    }
    // this form is called when we're doing fake blocking; so cannot
    // call get() directly and block;
    // instead, spawn a helper thread that will do the blocking call
    // and return
    sc_spawn_options op;
    char name[1024];
    sprintf(name, "get_bitstream_request_helper_%d", call_id);
    MARK_THREAD_INVISIBLE(op);
    sc_core::sc_spawn(sc_bind(&get_bitstream_request_helper,
                              rec,
                              call_id,
                              callback_adapter_id
                             ),
                      name, 
                      &op
                     );
    EXIT_CO_SIMULATION_CONTEXT();
    return 0;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_INT


  return 0;
}

unsigned uvm_ml_tlm_rec::get_requested(
    unsigned connector_id, 
    unsigned call_id , 
    uvm_ml_stream_t stream
) {
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT2();
    rec = get_receiver_base(connector_id);
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    void* p_call_id = (void*)(unsigned long)call_id;
    uvm_ml_packed_obj* retval = call_id_rec_dict[p_call_id];
    unsigned size =  uvm_ml_utils::copy_from_mlupo(*retval, stream);

    uvm_ml_utils::release_mlupo_to_pool(retval);
    EXIT_CO_SIMULATION_CONTEXT();
    return size;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

int uvm_ml_tlm_rec::nb_get(
  unsigned connector_id, 
  unsigned * stream_size_ptr,
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) {
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    int i = rec->try_get_bitstream(stream_size_ptr, stream);
    EXIT_CO_SIMULATION_CONTEXT();
    return i;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

int uvm_ml_tlm_rec::can_get(
  unsigned connector_id, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    int i = rec->can_get();
    EXIT_CO_SIMULATION_CONTEXT();
    return i; 
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

// peek takes part in disable protocol as it is blocking,
// so exception catching is more specialized
int uvm_ml_tlm_rec::peek(
  unsigned connector_id, 
  unsigned* stream_size_ptr,
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit * time_unit, 
  double           * time_value
) { 
    ENTER_CO_SIMULATION_CONTEXT2();
  int ret = 0;
  EXCEPTION_HANDLER_STORAGE();
  char msg[1024];
  sprintf(msg, "\nTLM function is peek");
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      STORE_OLD_EXCEPTION_HANDLER();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        RESTORE_OLD_EXCEPTION_HANDLER();
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    ret = rec->peek_bitstream(stream_size_ptr, stream);
    RESTORE_OLD_EXCEPTION_HANDLER();
    EXIT_CO_SIMULATION_CONTEXT();
    return ret;
  } 
  SC_KILL_CATCHER()
  catch( const sc_report& ex ) {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_PRINT_REPORT(ex);
    report_tlm1_error(rec);
    return ret;
  }
  catch( const ::std::exception& x )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_REPORT_COMPOSE_MESSAGE(x);
    report_tlm1_error(rec);
    return ret;
  }
  catch( const char* s )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
    cout << "\n" << s << "\n";
    report_tlm1_error(rec);
    return ret;
  }
  EXIT_CO_SIMULATION_CONTEXT();
  return ret;
}

void peek_bitstream_request_helper(
  uvm_ml_tlm_receiver_base* rec,
  unsigned call_id,
  unsigned callback_adapter_id
) {
  try {
    MLUPO* retval = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::allocate_mlupo(retval);
    // call blocking get()
    rec->peek_bitstream(&(retval->size), retval->val);
    // when get() returns, first hash return value with call id be 
    // retrieved later thru get_requested_bitstream()
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void*)(unsigned long)call_id;
    call_id_rec_dict.insert(p_call_id, retval);
    // callback into source adapter
    // to inform that call has ended
    uvm_ml_tlm_trans::notify_end_blocking(callback_adapter_id, call_id);
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_3
}

int uvm_ml_tlm_rec::request_peek(
  unsigned connector_id, 
  unsigned call_id,
  unsigned callback_adapter_id, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) {
        EXIT_CO_SIMULATION_CONTEXT();
      return 0;
    }
    // this form is called when we're doing fake blocking; so cannot
    // call peek() directly and block;
    // instead, spawn a helper thread that will do the blocking call
    // and return
    sc_spawn_options op;
    char name[1024];
    sprintf(name, "peek_bitstream_request_helper_%d", call_id);
    MARK_THREAD_INVISIBLE(op);
    sc_core::sc_spawn(sc_bind(&peek_bitstream_request_helper,
                              rec,
                              call_id,
                              callback_adapter_id
                             ),
                      name, 
                      &op
                     );
    EXIT_CO_SIMULATION_CONTEXT();
    return 0;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_INT

  return 0;
}

unsigned uvm_ml_tlm_rec::peek_requested (
  unsigned connector_id,
  unsigned call_id,
  uvm_ml_stream_t stream
) {
  uvm_ml_tlm_receiver_base* rec = get_receiver_base(connector_id);
  try {
      ENTER_CO_SIMULATION_CONTEXT2();
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    void* p_call_id = (void*)(unsigned long)call_id;
    uvm_ml_packed_obj* retval = call_id_rec_dict[p_call_id];
    unsigned size =  uvm_ml_utils::copy_from_mlupo(*retval, stream);
    //delete retval;
    uvm_ml_utils::release_mlupo_to_pool(retval);
    EXIT_CO_SIMULATION_CONTEXT();
    return size;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

    

int uvm_ml_tlm_rec::nb_peek(
  unsigned connector_id, 
  unsigned * stream_size_ptr,
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) {
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    int i = rec->try_peek_bitstream(stream_size_ptr, stream);
    EXIT_CO_SIMULATION_CONTEXT();
    return i;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

int uvm_ml_tlm_rec::can_peek(
  unsigned connector_id, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0;
    }
    int i = rec->can_peek();
    EXIT_CO_SIMULATION_CONTEXT();
    return i; 
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

// transport_bitstream takes part in disable protocol as it is blocking,
// so exception catching is more specialized

int uvm_ml_tlm_rec::transport(
    unsigned connector_id, 
    unsigned req_stream_size, 
    uvm_ml_stream_t req_stream,
    unsigned* rsp_stream_size, 
    uvm_ml_stream_t rsp_stream, 
  uvm_ml_time_unit * time_unit, 
  double           * time_value
) {
    ENTER_CO_SIMULATION_CONTEXT2();
  int ret = 0;
  EXCEPTION_HANDLER_STORAGE();
  char msg[1024];
  sprintf(msg, "\nTLM function is transport");
  uvm_ml_tlm_receiver_base* rec = 0;

  try {
      STORE_OLD_EXCEPTION_HANDLER();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        RESTORE_OLD_EXCEPTION_HANDLER();
        EXIT_CO_SIMULATION_CONTEXT();
      return 0; 
    }
    ret = rec->transport_bitstream(
      req_stream_size, 
      req_stream,
      rsp_stream_size, 
      rsp_stream
    );
    RESTORE_OLD_EXCEPTION_HANDLER();
    EXIT_CO_SIMULATION_CONTEXT();
    return ret;
  } 
  SC_KILL_CATCHER()
  catch( const sc_report& ex ) {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_PRINT_REPORT(ex);
    report_tlm1_error(rec);

    return ret;
  }
  catch( const ::std::exception& x )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_REPORT_COMPOSE_MESSAGE(x);
    report_tlm1_error(rec);

    return ret;
  }
  catch( const char* s )
  {
      RESTORE_OLD_EXCEPTION_HANDLER();
      EXIT_CO_SIMULATION_CONTEXT();
    cout << "\n" << s << "\n";
    report_tlm1_error(rec);
    //sc_get_curr_simcontext()->set_error();
    return ret;
  }
  EXIT_CO_SIMULATION_CONTEXT();
  return ret;
}

void transport_bitstream_request_helper(
  uvm_ml_tlm_receiver_base* rec,
  unsigned call_id,
  unsigned callback_adapter_id,
  MLUPO* mlupo_req_stream 
) {
  try {
    MLUPO* rspval = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::allocate_mlupo(rspval);
    // call blocking transport()
    rec->transport_bitstream(
      mlupo_req_stream->size,
      mlupo_req_stream->val,
      &(rspval->size), 
      rspval->val
    );
    // when transport() returns, first hash return value with call id to be 
    // retrieved later thru transport_response_bitstream()
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void*)(unsigned long)call_id;
    call_id_rec_dict.insert(p_call_id, rspval);
    // callback into source adapter
    // to inform that call has ended
    uvm_ml_tlm_trans::notify_end_blocking(callback_adapter_id, call_id);
    //delete mlupo_req_stream;
    uvm_ml_utils::release_mlupo_to_pool(mlupo_req_stream);
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_3
}

int uvm_ml_tlm_rec::request_transport(
    unsigned connector_id, 
    unsigned call_id, 
    unsigned callback_adapter_id, 
    unsigned req_stream_size, 
    uvm_ml_stream_t req_stream,
    unsigned* rsp_stream_size, 
    uvm_ml_stream_t rsp_stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
)  {
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) {
        EXIT_CO_SIMULATION_CONTEXT();
      return 0 ;
    }
    // this form is called when we're doing fake blocking; so cannot
    // call transport() directly and block;
    // instead, spawn a helper thread that will do the blocking call
    // and return
    sc_spawn_options op;
    char name[1024];
    sprintf(name, "transport_bitstream_request_helper_%d", call_id);
    MARK_THREAD_INVISIBLE(op);

    // copy the req_stream into a mlupo. This is necessary because it is 
    // likely that in backplane, they use the same stream for 
    // multiple calls - so for back to back calls the arguments will get
    // overwritten until we make a copy here;
    // the helper will delete the mlupo we allocate here when it is done
  
    //MLUPO* mlupo_req_stream = new MLUPO;
    MLUPO* mlupo_req_stream = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::fill_mlupo(*mlupo_req_stream,req_stream_size,req_stream);

    sc_core::sc_spawn(sc_bind(&transport_bitstream_request_helper,
                              rec,
                              call_id,
                              callback_adapter_id,
                              mlupo_req_stream
                             ),
                      name, 
                      &op
                     );
    EXIT_CO_SIMULATION_CONTEXT();
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_INT

  return 0;
}

unsigned uvm_ml_tlm_rec::transport_response(
  unsigned            connector_id,
  unsigned            call_id,
  uvm_ml_stream_t rsp_stream 
) {
  uvm_ml_tlm_receiver_base* rec = get_receiver_base(connector_id);
  try {
      ENTER_CO_SIMULATION_CONTEXT2();
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    void* p_call_id = (void*)(unsigned long)call_id;
    uvm_ml_packed_obj* rspval = call_id_rec_dict[p_call_id];
    unsigned size =  uvm_ml_utils::copy_from_mlupo(*rspval, rsp_stream);
    //delete rspval;
    uvm_ml_utils::release_mlupo_to_pool(rspval);
    EXIT_CO_SIMULATION_CONTEXT();
    return size;
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1
}

int uvm_ml_tlm_rec::nb_transport(
    unsigned connector_id, 
    unsigned req_stream_size, 
    uvm_ml_stream_t req_stream,
    unsigned* rsp_stream_size, 
    uvm_ml_stream_t rsp_stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) {
    cerr << "Unimplemented: uvm_ml_tlm_rec::nb_transport_bitstream, "
         << "should not be here!!!!!" << endl;
  return 0;
}

void uvm_ml_tlm_rec::write(
  unsigned connector_id, 
  unsigned stream_size , 
  uvm_ml_stream_t stream, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) { 
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    rec = get_receiver_base(connector_id);
    if (!rec) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return; 
    }
    rec->write_bitstream(stream_size,stream);
    EXIT_CO_SIMULATION_CONTEXT();
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_VOID
}

void uvm_ml_tlm_rec::notify_end_blocking(
  unsigned call_id, 
  uvm_ml_time_unit time_unit, 
  double           time_value
) {
  uvm_ml_tlm_receiver_base* rec = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT3();
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    void* p_call_id = (void*)(unsigned long)call_id;
    sc_event* e = call_id_trans_dict[p_call_id];
    if (!e) {
        EXIT_CO_SIMULATION_CONTEXT5();
        SC_REPORT_ERROR(ML_UVM_UNKNOWN_CALL_ID_, 0);
    }
    e->notify(); // will cause calling SC thread to get scheduled
    EXIT_CO_SIMULATION_CONTEXT4();
  }
  CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_VOID
}

//////////////////////

// TLM2

int uvm_ml_tlm_rec::tlm2_b_transport(
    unsigned              connector_id, 
    unsigned *            stream_size,
    uvm_ml_stream_t * stream,
    uvm_ml_time_unit *    delay_unit,
    double *              delay_value,
    uvm_ml_time_unit      time_unit, 
    double                time_value
) {
  ml_tlm2_connector_base* conn = 0;

  try {
      ENTER_CO_SIMULATION_CONTEXT();
    conn = uvm_ml_utils::get_ml_tlm2_connector_base(connector_id);
    if (!conn) { 
      EXIT_CO_SIMULATION_CONTEXT();
      return 1; // TBD FIXME
    }
    //assert(conn->is_target);
    if(!(conn->is_target)) {
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: tlm2_b_transport connector is not target","");
      return 1;
    };
    ml_tlm2_target_connector_base *target_conn = dynamic_cast<ml_tlm2_target_connector_base *>(conn);
    
    // Create MLUPO from stream
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,*stream_size,*stream);
    
    target_conn->b_transport(vt, (sc_time_unit *) delay_unit, delay_value, (sc_time_unit)time_unit, time_value);
    // Check that the incoming stream is big enough to store the 
    // transaction on the return path
    if (vt.size > *stream_size) 
      *stream = new unsigned[vt.size/UVM_ML_BLOCK_SIZE];
    // it is the caller's responsibility to deallocate both streams
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, *stream);    


    EXIT_CO_SIMULATION_CONTEXT2();
    return 0;
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_4
}

void uvm_ml_tlm_rec::tlm2_transport_request_helper(
  ml_tlm2_target_connector_base* conn,
  unsigned                       call_id,
  unsigned                       callback_adapter_id,
  MLUPO                        * mlupo_req_stream,
  sc_time_unit                   delay_unit, 
  double                         delay_value,
  sc_time_unit                   time_unit, 
  double                         time_value
) {
  try {
    conn->b_transport(
      *mlupo_req_stream,
      &delay_unit,
      &delay_value,
      time_unit,
      time_value
    );
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    void* p_call_id = (void*)(unsigned long)call_id;
    call_id_rec_dict.insert(p_call_id, mlupo_req_stream);
    call_id_delay_unit_dict[call_id] = delay_unit;
    call_id_delay_value_dict[call_id] = delay_value;
    // callback into source adapter to inform that call has ended
    uvm_ml_tlm_trans::notify_end_blocking(callback_adapter_id, call_id);
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_3
}

int uvm_ml_tlm_rec::tlm2_b_transport_request(
    unsigned            connector_id, 
    unsigned            call_id,
    unsigned            callback_adapter_id,
    unsigned            stream_size,
    uvm_ml_stream_t stream,
    uvm_ml_time_unit   delay_unit,
    double              delay_value,
    uvm_ml_time_unit    time_unit, 
    double              time_value
) {
  ml_tlm2_target_connector_base* conn = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT();
    conn = dynamic_cast<ml_tlm2_target_connector_base *>(uvm_ml_utils::get_ml_tlm2_connector_base(connector_id));
    if (!conn) {
        EXIT_CO_SIMULATION_CONTEXT();
        return 1; // TBD FIXME - 1 indicates disabled threads not an internal error
    }
    ml_tlm2_target_connector_base *target_conn = dynamic_cast<ml_tlm2_target_connector_base *>(conn);

    // this form is called when we're doing fake blocking; so cannot
    // call transport() directly and block;
    // instead, spawn a helper thread that will do the blocking call
    // and return
    sc_spawn_options op;
    char name[1024];
    sprintf(name, "tlm2_transport_request_helper_%d", call_id);
    MARK_THREAD_INVISIBLE(op);

    // copy the req_stream into a mlupo. This is necessary because it is 
    // likely that in backplane, they use the same stream for 
    // multiple calls - so for back to back calls the arguments will get
    // overwritten unless we make a copy here;
    // the helper will delete the mlupo we allocate here when it is done
  
    MLUPO* mlupo_req_stream = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::fill_mlupo(*mlupo_req_stream,stream_size,stream);

    sc_core::sc_spawn(sc_bind(&tlm2_transport_request_helper,
                              conn,
                              call_id,
                              callback_adapter_id,
                              mlupo_req_stream,
                              (sc_time_unit)delay_unit,
                              delay_value,
                              (sc_time_unit)time_unit,
                              time_value
                             ),
                      name, 
                      &op
                     );
    EXIT_CO_SIMULATION_CONTEXT2();
    return 0; // TBD FIXME - support disabling of the threads
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_4
}

int uvm_ml_tlm_rec::tlm2_b_transport_response(
    unsigned              connector_id, 
    unsigned              call_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream
) {
  ml_tlm2_target_connector_base* conn = 0;
  try {
      ENTER_CO_SIMULATION_CONTEXT2();
    conn = dynamic_cast<ml_tlm2_target_connector_base *>(uvm_ml_utils::get_ml_tlm2_connector_base(connector_id));
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long matches the size of pointers on 32 bit and 64 bit m/cs
    void* p_call_id = (void*)(unsigned long)call_id;
    uvm_ml_packed_obj* rspval = call_id_rec_dict[p_call_id];
    *stream_size =  uvm_ml_utils::copy_from_mlupo(*rspval, *stream);
    uvm_ml_utils::release_mlupo_to_pool(rspval);
    EXIT_CO_SIMULATION_CONTEXT();
    return 0;
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_4
}

uvm_ml_tlm_sync_enum uvm_ml_tlm_rec::tlm2_nb_transport_fw(
    unsigned              connector_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream,
    uvm_ml_tlm_phase *   phase,
    unsigned int          transaction_id,
    uvm_ml_time_unit *   delay_unit,
    double *              delay_value,
    uvm_ml_time_unit      time_unit, 
    double                time_value
) {
  ml_tlm2_connector_base* conn = 0;
  tlm_sync_enum ret;

  try {
      ENTER_CO_SIMULATION_CONTEXT();
    conn = uvm_ml_utils::get_ml_tlm2_connector_base(connector_id);
    if (!conn) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return UVM_ML_TLM2_COMPLETED; // return error code
    }
    //assert(conn->is_target);
    if(!(conn->is_target)) {
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: tlm2_nb_transport_fw connector is not target","");
      return UVM_ML_TLM2_COMPLETED; // return error code
    };
    ml_tlm2_target_connector_base *target_conn = dynamic_cast<ml_tlm2_target_connector_base *>(conn);
    
    // Create MLUPO from stream
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,*stream_size,*stream);
    
    ret = target_conn->nb_transport_fw(vt, (tlm_phase_enum *) phase, transaction_id, (sc_time_unit *) delay_unit, delay_value, (sc_time_unit)time_unit, time_value);
    // Check that the incoming stream is big enough to store the 
    // transaction on the return path
    if (vt.size > *stream_size) 
      *stream = new unsigned[vt.size/UVM_ML_BLOCK_SIZE];
    // it is the caller's responsibility to deallocate both streams
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, *stream);    
    EXIT_CO_SIMULATION_CONTEXT();
    return (uvm_ml_tlm_sync_enum) ret;
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_1
}

uvm_ml_tlm_sync_enum uvm_ml_tlm_rec::tlm2_nb_transport_bw(
    unsigned              connector_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream,
    uvm_ml_tlm_phase *   phase,
    unsigned int          transaction_id,
    uvm_ml_time_unit *    delay_unit,
    double *              delay_value,
    uvm_ml_time_unit      time_unit, 
    double                time_value
) {
  ml_tlm2_connector_base* conn = 0;
  tlm_sync_enum ret;

  try {
      ENTER_CO_SIMULATION_CONTEXT();
    conn = uvm_ml_utils::get_ml_tlm2_connector_base(connector_id);
    if (!conn) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return UVM_ML_TLM2_COMPLETED; // return error code
    }
    //assert(!conn->is_target);
    if(conn->is_target) {
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: tlm2_nb_transport_bw connector is not target","");
      return UVM_ML_TLM2_COMPLETED; // return error code
    };
    ml_tlm2_initiator_connector_base *initiator_conn = dynamic_cast<ml_tlm2_initiator_connector_base *>(conn);
    
    // Create MLUPO from stream
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,*stream_size,*stream);
    
    ret = initiator_conn->nb_transport_bw(vt, (tlm_phase_enum *)phase, transaction_id, (sc_time_unit *)delay_unit, delay_value, (sc_time_unit)time_unit, time_value);
    // Check that the incoming stream is big enough to store the 
    // transaction on the return path
    if (vt.size > *stream_size) 
      *stream = new unsigned[vt.size/UVM_ML_BLOCK_SIZE];
    // it is the caller's responsibility to deallocate both streams
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, *stream);
    
    EXIT_CO_SIMULATION_CONTEXT();
    return (uvm_ml_tlm_sync_enum) ret;
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_1
}

unsigned uvm_ml_tlm_rec::tlm2_transport_dbg(
    unsigned              connector_id,
    unsigned *            stream_size,
    uvm_ml_stream_t * stream,
    uvm_ml_time_unit      time_unit, 
    double                time_value
) {
  ml_tlm2_connector_base* conn = 0;
  unsigned ret;

  try {
      ENTER_CO_SIMULATION_CONTEXT();
    conn = uvm_ml_utils::get_ml_tlm2_connector_base(connector_id);
    if (!conn) { 
        EXIT_CO_SIMULATION_CONTEXT();
      return 0;
    }
    //assert(conn->is_target);
    if(!(conn->is_target)) {
      EXIT_CO_SIMULATION_CONTEXT();
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: tlm2_transport_dbg connector is not target","");
      return 0; // return error code
    };
    ml_tlm2_target_connector_base *target_conn = dynamic_cast<ml_tlm2_target_connector_base *>(conn);
    
    // Create MLUPO from stream
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,*stream_size,*stream);
    
    ret = target_conn->transport_dbg(vt, (sc_time_unit)time_unit, time_value);
    if (vt.size > *stream_size) 
      *stream = new unsigned[vt.size/UVM_ML_BLOCK_SIZE];
    // it is the caller's responsibility to deallocate both streams
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, *stream);

    EXIT_CO_SIMULATION_CONTEXT();
    return ret;
  }
  CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_1
}


void uvm_ml_tlm_rec::tlm2_turn_off_transaction_mapping(const char *socket_name) {
    ml_tlm2_turn_off_transaction_mapping(socket_name);  
}

void uvm_ml_tlm_rec::synchronize(uvm_ml_time_unit time_unit, 
                                 double           time_value) {

  ENTER_CO_SIMULATION_CONTEXT();
  EXIT_CO_SIMULATION_CONTEXT();
}


int uvm_ml_tlm_rec::create_child_junction_node(const char * component_type_name,
                                               const char * instance_name,
                                               const char * parent_full_name,
                                               int          parent_framework_id,
                                               int          parent_junction_node_id) {

    // The parent proxy with the given parent_full_name might already exist if the parent junction node
    // instantiates multiple SystemC child components. Hence. first thing, check if it exists:
    string parentFullName = string(parent_full_name);
    parent_component_proxy * proxy = uvm_ml_utils::find_parent_proxy_by_id(parent_junction_node_id);
    if (proxy == NULL)
        proxy = parent_component_proxy::create(parentFullName, parent_framework_id, parent_junction_node_id);
    return proxy->add_node(component_type_name, instance_name);
}

static void * backplane_handle = NULL;

static const char* const backplane_get_provided_tray = "bp_get_provided_tray";


static void backplane_open()
{
    // The backplane library may be compiled in or preloaded
    // So, start with the 'global' namespace
    backplane_handle  = dlopen(0, RTLD_LAZY);
    
    if ( backplane_handle != 0) {
        if ( dlsym(backplane_handle, backplane_get_provided_tray) != 0) {
            return;
        }
    }

    const char* const backplane_lib_name = "libml_uvm.so";

    char * lib_location = getenv("UVM_ML_OVERRIDE");

    if (lib_location == NULL) { 
        lib_location = getenv("UNILANG_OVERRIDE");
    }

    if (lib_location) {
        backplane_handle  = dlopen(((string)lib_location + "/"+backplane_lib_name).c_str(), RTLD_LAZY | RTLD_GLOBAL);
    } else {
        backplane_handle  = dlopen(backplane_lib_name, RTLD_LAZY | RTLD_GLOBAL);
    }

    if (backplane_handle == NULL) {
        string err_str = (char *) dlerror();

        // FIXME - use proper error messaging and proper per-simulator graceful shutdown mechanism here

        ::std::cout << "Failed to open the backplane library " << backplane_lib_name << " for the following reason: " << err_str << ::std::endl;
        exit(0);
    }

}


} // namespace uvm_ml
//////////////////////

EXTERN_DISABLE_SC_START;

// return 0 for error
unsigned uvm_ml_utils::initialize_adapter()
{
    backplane_open();

    //assert(backplane_handle != NULL);
    if(backplane_handle == NULL) {
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: backplane not initialized","");
      return 0; // return error code
    };

    bp_api_struct* (*bp_get_provided_tray_ptr)() = (bp_api_struct* (*)())dlsym(backplane_handle, backplane_get_provided_tray);
    bpProvidedAPI = (bp_get_provided_tray_ptr)();
    //assert(bpProvidedAPI != NULL);
    if(bpProvidedAPI == NULL) {
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: backplane provided API not available","");
      return 0; // return error code
    };
    char *frmw_ids[3] = {(char*)"UVMSC", (char*)"SC",(char*)""};
    DISABLE_SC_START();

    uvm_ml_phase::Initialize(bpProvidedAPI);        // Initialize phasing
    uvm_ml_config_rsrc::Initialize(bpProvidedAPI);  // Initialize config/rsrc

    return BP(register_framework)((char*)"SystemC",frmw_ids, uvm_ml_sc_get_required_api());
}

//////////////////////
unsigned uvm_ml_utils::get_type_id(std::string name) {
    return BP(get_type_id_from_name)(framework_id, (char*)name.c_str());
}

char* uvm_ml_utils::get_type_name(unsigned id) {
    return BP(get_type_name_from_id)(framework_id, id);
}

unsigned int uvm_ml_utils::assign_transaction_id() {
    return BP(assign_transaction_id)(framework_id);
}

//////////////////////


namespace uvm_ml {

  void uvm_ml_connect(const std::string & port_name, const std::string & export_name, bool map_transactions) {
        if (IN_ELABORATION()) return;
        if (! ml_tlm2_check_cross_registration(port_name, export_name)) return;
        if (uvm_ml_utils::quasi_static_construction_ended()) {
	    unsigned result = uvm_ml_utils::do_connect(port_name, export_name);
	    if(result == 0) return; // propagate error
            if (map_transactions == false) {
	        uvm_ml_utils::tlm2_turn_off_transaction_mapping(port_name, export_name);
            }
        } else {
            uvm_ml_utils::add_pending_uvm_ml_connect_call(port_name, export_name, map_transactions);
        }
    }

//------------------------------------------------------------------------------
//! Calls backplane to register which framework will provide which service.
/*!
 *  @param srv_providers - List of fields populated with name of framework 
 *                         providing the service.  Null fields are ignored 
 *                         by the backplane. 
 */
  void uvm_ml_register_srv_providers(uvm_ml_srv_provider_struct * srv_providers)
  {
      bp_srv_provider_struct * bp_srv_providers;

      bp_srv_providers = (bp_srv_provider_struct *) (srv_providers);
      BP(register_srv_providers)(framework_id, bp_srv_providers);
  }

} // namespace uvm_ml


//////////////////////

uvm_ml_tlm_transrec_base::uvm_ml_tlm_transrec_base(const char* name_) 
    //: sc_object(name_) 
{
  m_obj = 0;
  m_id_is_valid = false;
  m_intf_name = "unknown_interface";
  m_REQ_name = "unknown_type";
  m_RSP_name = "unknown_type";
}

uvm_ml_tlm_transrec_base::~uvm_ml_tlm_transrec_base() { }

sc_object* uvm_ml_tlm_transrec_base::object() const { return m_obj; }


bool uvm_ml_tlm_transrec_base::id_is_valid() const {
  return m_id_is_valid;
}

void uvm_ml_tlm_transrec_base::id_is_valid(bool b) {
  m_id_is_valid = b;
}

unsigned uvm_ml_tlm_transrec_base::connection_id() const { 
  return uvm_ml_utils::uvm_ml_tlm_id_from_name(m_obj->name()); 
}

std::string uvm_ml_tlm_transrec_base::get_intf_name() const {
  return m_intf_name;
}

std::string uvm_ml_tlm_transrec_base::get_REQ_name() const {
  return m_REQ_name;
}

std::string uvm_ml_tlm_transrec_base::get_RSP_name() const {
  return m_RSP_name;
}

void uvm_ml_tlm_transrec_base::set_intf_name(std::string s) {
  m_intf_name = s;
}

void uvm_ml_tlm_transrec_base::set_REQ_name(std::string s) {
  m_REQ_name = s;
}

void uvm_ml_tlm_transrec_base::set_RSP_name(std::string s) {
  m_RSP_name = s;
}

void uvm_ml_tlm_transrec_base::unconnected_error() const {
  char msg[1024];
  sprintf(msg, "\nPort/export is '%s'", m_obj->name());
  SC_REPORT_ERROR(ML_UVM_UNCONNECTED_ID_, msg);
}

//////////////////////

uvm_ml_tlm_transmitter_base::uvm_ml_tlm_transmitter_base(const char* name_)
    : uvm_ml_tlm_transrec_base(name_) { }

uvm_ml_tlm_transmitter_base::~uvm_ml_tlm_transmitter_base() { }

bool uvm_ml_tlm_transmitter_base::is_transmitter() const { return true; }

//////////////////////

uvm_ml_tlm_receiver_base::uvm_ml_tlm_receiver_base(const char* name_)
    : uvm_ml_tlm_transrec_base(name_) { }

uvm_ml_tlm_receiver_base::~uvm_ml_tlm_receiver_base() { }

bool uvm_ml_tlm_receiver_base::is_transmitter() const { return false; }


sc_interface* uvm_ml_tlm_receiver_base::get_interface() const { 
  return m_iface; 
}

//////////////////////

int uvm_ml_utils::get_pack_block_size() {
    return UVM_ML_PACKING_BLOCK_SIZE_INT;
}

int uvm_ml_utils::get_max_bits() {
  static int pack_block_size = get_pack_block_size();
  int size = BP(get_pack_max_size)(framework_id);
  if (size == -1) { // uninitilaized in backplane
    char* c = 0;
    c = getenv("UVM_ML_BITSIZE");
    if (c) {
      size = atoi(c);
    }
    if (size < pack_block_size) {
      size = pack_block_size;
    }
  }
  return size;
}

int round_bits(int nbits) {
  static unsigned pack_block_size = uvm_ml_utils::get_pack_block_size();
  //int i = (nbits - 1)/UVM_PACKING_BLOCK_SIZE + 1;
  //int n = i*UVM_PACKING_BLOCK_SIZE;
  int i = (nbits - 1)/pack_block_size + 1;
  int n = i*pack_block_size;
  return n;
}

int uvm_ml_utils::get_max_words() {
  static int max_bits = uvm_ml_utils::get_max_bits();
  static int round_max_bits = round_bits(max_bits);
  static int max_words = 1 + (round_max_bits - 1)/32;
  return max_words;
}

void uvm_ml_utils::fill_mlupo(MLUPO& vt, unsigned size, void* stream) {
  int nwords;
  vt.size = size;
  uvm_ml_stream_t val = (uvm_ml_stream_t)stream;
  nwords = size/UVM_ML_BLOCK_SIZE;
  int round_nbits = round_bits(nwords*32);
  int alloc_words = 1 + (round_nbits - 1)/32;

  // we could for simplicity also allocatethe max_words here, although
  // that is not necessary
 
  // we are always allocate mlupo in multiples of UVM_PACKING_BLOCK_SIZE;
  // not really necessary; optimize in future

  uvm_ml_packed_obj::allocate(&vt, alloc_words);

  memcpy(vt.val, val, nwords*sizeof(unsigned));
}


void uvm_ml_utils::allocate_mlupo(MLUPO* vt) {
  static int max_bits = uvm_ml_utils::get_max_bits();

  static int alloc_words = uvm_ml_utils::get_max_words();
   

  // we are always allocating mlupo in multiples of UVM_PACKING_BLOCK_SIZE;
  // not really necessary; optimize in future

  uvm_ml_packed_obj::allocate(vt, alloc_words);
}

unsigned uvm_ml_utils::copy_from_mlupo(const MLUPO& vt, void* stream) {
    int nwords;
    unsigned* ustream = (unsigned*)stream;
    nwords = vt.size/UVM_ML_BLOCK_SIZE;
    memcpy(ustream, vt.val, nwords*sizeof(unsigned));

    return vt.size;
}


uvm_ml_packed_obj static_mlupo;

uvm_ml_packed_obj& uvm_ml_utils::get_static_mlupo() {
  return static_mlupo;
}

std::queue<uvm_ml_packed_obj*> mlupo_free_q;

uvm_ml_packed_obj* uvm_ml_utils::get_mlupo_from_pool() {
  uvm_ml_packed_obj* n = 0;
  int size = mlupo_free_q.size();
  if (size > 0) {
    n = mlupo_free_q.front();
    mlupo_free_q.pop();
    return n;
  }
  // allocate new mlupo
  //cout << "**************allocating new mlupo " << endl;
#ifdef _NCSC_DEBUG
  dbginfo(U) << "**************allocating new mlupo " << endl;
#endif
  n = new uvm_ml_packed_obj();
  return n;
}
  
void uvm_ml_utils::release_mlupo_to_pool(uvm_ml_packed_obj* n) {
  mlupo_free_q.push(n);
}

void uvm_ml_utils::register_static_top(const string & top_name) {

  if (IN_ELABORATION()) return; // don't attempt calling the backplane during static elaboration

  if (quasi_static_elaboration_started()) return; // Quasi-static tops should be registered separately

  if (std::find(static_top_names.begin(), static_top_names.end(), top_name) != static_top_names.end())
    return; // Already registered 

  if (BP(add_root_node)(framework_id,
                        get_next_top_id(),
                        top_name.c_str(),
                        top_name.c_str()) == (-1))
      SC_REPORT_ERROR(ML_UVM_RUN_TIME_ERROR_,"Duplicate top component instance name ");

  static_top_names.push_back(top_name);
}

unsigned int uvm_ml_utils::add_quasi_static_tree_node(sc_module * pmod) { 
    quasi_static_tree_nodes.push_back (pmod); 
    return static_top_names.size() + quasi_static_tree_nodes.size() - 1; 
};

//////

/*! \class uvm_ml_tlm_connection_info
  \brief Maintains information about an interface.

  
*/
class uvm_ml_tlm_connection_info {
public:
    uvm_ml_tlm_connection_info(const std::string & port_name, const std::string & export_name, bool map_transactions = true):  
        m_port_name(port_name), m_export_name(export_name), m_map_transactions(map_transactions)
    {
    }
    std::string m_port_name;
    std::string m_export_name;
    bool m_map_transactions;
};

typedef std::vector<uvm_ml_tlm_connection_info*> uvm_ml_tlm_connection_vec;

static uvm_ml_tlm_connection_vec* pending_uvm_ml_connect_calls = 0;

unsigned uvm_ml_utils::do_connect (const std::string & port_name, const std::string & export_name) {
    //assert (bpProvidedAPI != NULL);
    if(bpProvidedAPI == NULL) {
      char msg[1024];
      sprintf(msg, "\nPort is '%s'; Export is '%s' \n", port_name.c_str(), export_name.c_str());
      UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: do_connect failed",msg);
      return 0; // propagate error 
    };
    return BP(connect)(framework_id,port_name.c_str(),export_name.c_str());
}

void uvm_ml_utils::add_pending_uvm_ml_connect_call(const std::string & port_name,
                                                   const std::string & export_name, 
                                                   bool map_transactions) {
  if (!pending_uvm_ml_connect_calls) {
    pending_uvm_ml_connect_calls = new uvm_ml_tlm_connection_vec;
  }
  uvm_ml_tlm_connection_info* info = 
      new uvm_ml_tlm_connection_info(port_name, export_name, map_transactions);
  pending_uvm_ml_connect_calls->push_back(info);
}

void uvm_ml_utils::tlm2_turn_off_transaction_mapping(const std::string & port_name, 
                                                const std::string & export_name) {
    BP(turn_off_transaction_mapping)(framework_id, port_name.c_str());
    BP(turn_off_transaction_mapping)(framework_id, export_name.c_str());
}

int uvm_ml_utils::do_pending_uvm_ml_connect_calls() {

  int result = 1;
  if (pending_uvm_ml_connect_calls) {

      for (unsigned i = 0; i < pending_uvm_ml_connect_calls->size(); i++) {
          uvm_ml_tlm_connection_info* info = (*pending_uvm_ml_connect_calls)[i];
          result = uvm_ml_utils::do_connect(info->m_port_name, info->m_export_name);
          if (result && (info->m_map_transactions == false)) {
              tlm2_turn_off_transaction_mapping(info->m_port_name, info->m_export_name);
          }
      }
      pending_uvm_ml_connect_calls->clear();
  }
  return result;
}

// ///////////////////////

void uvm_ml_tlm_trans::request_put(
  unsigned port_connector_id,
  MLUPO* arg 
) {
  unsigned call_id = fake_blocking_call_id++;
  unsigned done = 0;
  int disable = BP(request_put)(
    framework_id,
    port_connector_id,
    call_id,
    arg->size,
    arg->val,
    &done,
    &m_time_unit,
    &m_time_value
  );
  if (!done) {
    //SC_REPORT_ERROR(UVM_DONE_BIT_,"");
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void *)(unsigned long)call_id;
    sc_event *e = new INVISIBLE_EVENT("uvm_fake_blocking");
    call_id_trans_dict.insert(p_call_id, e);
    sc_core::wait(*e);
    // we are here when the target adaptor has informed us via 
    // the backplane that the call has finished in it;
    // delete call_id and event ptrs
    delete e;
  }
  if (disable == 1) {
    // rule out the cases that 1) SC process initiated call (ECC) and child
    // SV is disabled; this is illegal at present
    // 2) e initiated call and somehow 1 is returned here
      uvm_ml::dpi_task_disabled();
  }
}

int uvm_ml_tlm_trans::nb_put(
  unsigned local_port_id, 
  MLUPO* val
) {
    return BP(nb_put)(
    framework_id,
    local_port_id,
    val->size,
    val->val,
    m_time_unit,
    m_time_value
  );
}

int uvm_ml_tlm_trans::can_put(unsigned local_port_id) {
    return BP(can_put)(framework_id,local_port_id, m_time_unit, m_time_value);
}

void uvm_ml_tlm_trans::notify_end_blocking(
  unsigned callback_adapter_id,
  unsigned call_id
) {
    BP(notify_end_blocking)(framework_id, callback_adapter_id, call_id, m_time_unit, m_time_value);
}

//

void uvm_ml_tlm_trans::request_get(
  unsigned port_connector_id,
  MLUPO* arg
) {
  unsigned call_id = fake_blocking_call_id++;
  unsigned done = 0;
  int disable = BP(request_get)(
    framework_id,
    port_connector_id,
    call_id,
    &(arg->size),
    arg->val,
    &done,
    &m_time_unit,
    &m_time_value
  );
  if (!done) { // fake blocking
    //SC_REPORT_ERROR(UVM_DONE_BIT_,"");
    // new sc_event; hash <call_id , event>; wait on event;
    // later target will cause event to be triggered
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void *)(unsigned long)call_id;
    sc_event* e = new INVISIBLE_EVENT("uvm_fake_blocking");
    call_id_trans_dict.insert(p_call_id, e);
    sc_core::wait(*e);
    // we are here when target adaptor has informed us via 
    // the backplane that the call has finished in it;
    // get the return value of get() from the backplane
    arg->size = BP(get_requested)(
      framework_id,
      port_connector_id,
      call_id,
      arg->val
    );
    // delete call_id and event ptrs
    delete e;
  }
  if (disable == 1) {
      uvm_ml::dpi_task_disabled();
  }
}

int uvm_ml_tlm_trans::nb_get(unsigned local_port_id, MLUPO* val) {
    return BP(nb_get)(
    framework_id, 
    local_port_id, 
    &(val->size),
    val->val,
    m_time_unit,
    m_time_value
  );
}

int uvm_ml_tlm_trans::can_get(unsigned local_port_id) {
    return BP(can_get)(framework_id, local_port_id, m_time_unit, m_time_value);
}

void uvm_ml_tlm_trans::request_peek(
  unsigned port_connector_id,
  MLUPO* arg
) {
  unsigned call_id = fake_blocking_call_id++;
  unsigned done = 0;
  int disable = BP(request_peek)(
    framework_id,
    port_connector_id,
    call_id,
    &(arg->size),
    arg->val,
    &done,
    &m_time_unit,
    &m_time_value
  );
  if (!done) {
    // new sc_event; hash <call_id , event>; wait on event;
    // later target will cause event to be triggered
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void *)(unsigned long)call_id;

    sc_event* e = new INVISIBLE_EVENT("uvm_fake_blocking");
    call_id_trans_dict.insert(p_call_id, e);
    sc_core::wait(*e);
    // we are here when the target framework has informed us via 
    // the backplane that the call has finished in it;
    // get the return value of get() from the backplane
    arg->size = BP(peek_requested)(
      framework_id,
      port_connector_id,
      call_id,
      arg->val
    );
    // delete call_id and event ptrs
    delete e;
  }
  if (disable == 1) {
      uvm_ml::dpi_task_disabled();
  }
}

int uvm_ml_tlm_trans::nb_peek(unsigned local_port_id, MLUPO* val) {
    return BP(nb_peek)(
    framework_id, 
    local_port_id, 
    &(val->size),
    val->val,
    m_time_unit,
    m_time_value
  );
}

int uvm_ml_tlm_trans::can_peek(unsigned local_port_id) {
    return BP(can_peek)(framework_id, local_port_id, m_time_unit, m_time_value);
}

int uvm_ml_tlm_trans::request_transport(
  unsigned port_connector_id,
  MLUPO* req,
  MLUPO* rsp
) {
  unsigned call_id = fake_blocking_call_id++;
  unsigned done = 0;
  int disable = BP(request_transport)(
    framework_id,
    port_connector_id,
    call_id,
    req->size,
    req->val,
    &(rsp->size),
    rsp->val,
    &done,
    &m_time_unit,
    &m_time_value
  );
  if (!done) {
    //SC_REPORT_ERROR(UVM_DONE_BIT_,"");
    // new sc_event; hash <call_id , event>; wait on event;
    // later target will cause event to be triggered
    void* p_call_id;
    // need to do the cast to unsigned long below before casting to pointer
    // because on 64 bit m/cs pointers are 64 bits, whereas unsigned is 32
    // bits; so casting from unsigned to pointer generates compiler warning;
    // unsigend long  matches the size of pointers on 32 bit and 64 bit m/cs
    p_call_id = (void *)(unsigned long)call_id;

    sc_event* e = new INVISIBLE_EVENT("uvm_fake_blocking");

    call_id_trans_dict.insert(p_call_id, e);
    sc_core::wait(*e);
    // we are here when target adaptor has informed us via
    // the backplane that the call has finished in it;
    // get the return value of get() from the backplane
    rsp->size = BP(transport_response)(
      framework_id,
      port_connector_id,
      call_id,
      rsp->val
    );
    // delete call_id and event ptrs
    delete e;
  }
  if (disable == 1) {
      uvm_ml::dpi_task_disabled();
  }

  return 0;
}

void uvm_ml_tlm_trans::write(
  unsigned local_port_id, 
  MLUPO* val
) {
    BP(write)(
    framework_id,
    local_port_id,
    val->size,
    val->val,
    m_time_unit,
    m_time_value
  );
}
