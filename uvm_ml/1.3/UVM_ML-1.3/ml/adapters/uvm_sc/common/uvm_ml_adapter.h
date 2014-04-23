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

/*! \mainpage UVM-SC adapter
 *
 * \section top UVM-SC adapter
 * The adapter implements the interface to the UVM-ML backplane.
 */
/*! \file uvm_ml_adapter.h
  \brief Adapter header defining the required and provided API.
*/
#ifndef UVM_ML_ADAPTER_H
#define UVM_ML_ADAPTER_H

#include "systemc.h"
#ifdef NC_SYSTEMC
#include "sysc/utils/sc_iostream.h"
#include "sysc/communication/sc_export.h"
#include "sysc/communication/sc_port.h"


#include "base/uvm_ids.h"
#include "sysc/cosim/ml_uvm_ids.h"
#include <typeinfo>
#include <stdio.h>
#else
#include "sysc/kernel/sc_simcontext.h"
#endif

#include "tlm.h"
#include <map>

#include "base/uvm_phase.h"


#include "uvm_ml_adapter_imp_spec_macros.h"
#include "uvm_ml_hierarchy.h"

#define UVM_ML_BLOCK_SIZE 32

/*! \struct uvm_ml_packed_obj
  \brief Struct containing the packed object.

  
*/
struct uvm_ml_packed_obj {
  unsigned size;
  unsigned *val;
  unsigned max_words;

  uvm_ml_packed_obj();
  ~uvm_ml_packed_obj(); 

  static void allocate(uvm_ml_packed_obj* obj, unsigned nwords);
};

///////////
namespace uvm_ml {

class ml_tlm2_connector_base; // forward declaration 


//! Structure containing fields of type const char *
/*! representing the name of the framework providing 
 *  the service.
 */
typedef struct uvm_ml_srv_provider_struct
{
    const char * phase_srv_provider;    ///< Name of framework providing the phase service

    uvm_ml_srv_provider_struct()
    {
        phase_srv_provider = "";
    }
} uvm_ml_srv_provider_struct;

extern bool ml_tlm2_check_cross_registration( 
    const std::string & port_name, 
    const std::string & export_name
);

void uvm_ml_connect(
    const std::string & port_name, 
    const std::string & export_name, 
    bool                map_transactions = true // For TLM2 connections only
);

child_component_proxy * uvm_ml_create_component(
    const std::string   & target_framework_indicator, 
    const std::string   & component_type_name, 
    const std::string   & instance_name,
    const uvm_component * parent
);
///////////////////


void uvm_ml_register_srv_providers (
    uvm_ml_srv_provider_struct * srv_providers
);

///////////////////

typedef uvm_ml_packed_obj MLUPO;

#ifndef NC_SYSTEMC
typedef sc_module* (*uvm_ml_new_module_func)(const char*);

static sc_strhash<uvm_ml_new_module_func>* new_module_funcs = 0;

int associate_module(const char*  name, uvm_ml_new_module_func f);
#endif

void ml_tlm2_turn_off_transaction_mapping(const char* socket_name);

typedef uvm_ml_packed_obj MLUPO;


/*! \class uvm_ml_tlm_conn_info
  \brief Maintain information about the connector.

  Maintain the connection between the name, id and the object itself
*/
class uvm_ml_tlm_conn_info {
public:
    /*! Constructor
      \param name The connection name
      \param id The connection ID
      \return N/A
    */
  uvm_ml_tlm_conn_info(std::string name, unsigned id);
  /*! The name() property
    \return std::string
  */
  std::string name() const { return m_name; }
  /*! The id() property
    \return unsigned int
  */
  unsigned id() const { return m_id; }
  /*! The object() property
    \return sc_object
  */
  sc_object* object() const { return m_object; }
protected:
  std::string m_name;
  unsigned m_id;
  sc_object* m_object;
  unsigned m_nextid;
};



///////////////////

/*! \class uvm_ml_tlm_trans
  \brief Implementation of the TLM1 and TLM2 methods and tasks.

  
*/
class uvm_ml_tlm_trans {
public:
  
  // put family

  static void request_put(
    unsigned port_connector_id, 
    MLUPO* val
  );
  static int nb_put(unsigned local_port_id, MLUPO* val);
  static int can_put(unsigned local_port_id);

  // get family

  static void request_get(
    unsigned port_connector_id, 
    MLUPO* val
  );
  static int nb_get(unsigned local_port_id, MLUPO* val);
  static int can_get(unsigned local_port_id);

  // peek family

  static void request_peek(
    unsigned port_connector_id, 
    MLUPO* val
  );
  static int nb_peek(unsigned local_port_id, MLUPO* val);
  static int can_peek(unsigned local_port_id);

  static int request_transport(
    unsigned port_connector_id, 
    MLUPO* req,
    MLUPO* rsp
  );

  static void write(unsigned local_port_id, MLUPO* val);

  static unsigned int tlm2_nb_transport_bw(
      unsigned         connector_id,
      MLUPO *          val,
      unsigned int *   phase,
      unsigned int     transaction_id,
      sc_time_unit *   delay_unit,
      double *         delay_value
      );

  static unsigned int tlm2_nb_transport_fw(
      unsigned         connector_id,
      MLUPO *          val,
      unsigned int *   phase,
      unsigned int     transaction_id,
      sc_time_unit *   delay_unit,
      double *         delay_value
      );

  static unsigned tlm2_transport_dbg(
      unsigned              connector_id,
      MLUPO *               val 
      );

  static void tlm2_b_transport(
      unsigned              connector_id,
      MLUPO *               val,
      sc_time_unit *        delay_unit,
      double *              delay_value
      );

  static void notify_end_blocking(
    unsigned callback_adapter_id, 
    unsigned call_id
  );
};

///////////////////

/*! \class uvm_ml_tlm_transrec_base
  \brief Base class for ML TLM interface.

  Maintains information about the interface attributes
*/
class uvm_ml_tlm_transrec_base {
public:
  uvm_ml_tlm_transrec_base(const char* name_);
  virtual ~uvm_ml_tlm_transrec_base();
  sc_core::sc_object* object() const;
  void object(sc_core::sc_object* b);
  unsigned connection_id() const;
  virtual bool is_transmitter() const = 0;
  virtual std::string get_intf_name() const;
  virtual std::string get_REQ_name() const;
  virtual std::string get_RSP_name() const;
  virtual void set_intf_name(std::string s); 
  virtual void set_REQ_name(std::string s); 
  virtual void set_RSP_name(std::string s); 
  bool id_is_valid() const;
  void id_is_valid(bool b);
  void unconnected_error() const;
protected:
  sc_core::sc_object* m_obj;
  std::string m_intf_name;
  std::string m_REQ_name;
  std::string m_RSP_name;
  bool m_id_is_valid;
};




///////////////////

/*! \class uvm_ml_tlm_transmitter_base
  \brief Base class for ML TLM transmitter interface.

  
*/
class uvm_ml_tlm_transmitter_base : public uvm_ml_tlm_transrec_base {
public:
  uvm_ml_tlm_transmitter_base(const char* name_);
  virtual ~uvm_ml_tlm_transmitter_base();
  virtual bool is_transmitter() const;
  virtual void register_port( sc_core::sc_port_base& port_, const char*) {
    this->object(&port_);
  }
};



/*! \class uvm_ml_utils
  \brief Utility functions for ML TLM interfaces.

  used by transmitters and receivers
*/
class uvm_ml_utils {

  friend class uvm_ml_tlm_rec;

public:
  static void register_static_top(const string & top_name);
  static int get_max_bits();
  static int get_max_words();
  static unsigned initialize_adapter();
  static unsigned FrameworkId();
  static unsigned uvm_ml_tlm_id_from_name(std::string name);
  static void fill_mlupo(MLUPO& vt, unsigned size, void* stream);
  static unsigned copy_from_mlupo(const MLUPO& vt, void* stream);
  static void allocate_mlupo(MLUPO* vt);

  static unsigned do_connect (const std::string & port_name, 
                              const std::string & export_name);

  // for delayed uvm_ml_connect calls
  static void add_pending_uvm_ml_connect_call(const std::string & port_name,
                                              const std::string & export_name,
                                              bool                map_transactions = true // valid for TLM2 calls only
  );

  static int do_pending_uvm_ml_connect_calls();

  static MLUPO& get_static_mlupo();
  static MLUPO* get_mlupo_from_pool();
  static void release_mlupo_to_pool(MLUPO* n);

  static int get_pack_block_size();

  static unsigned get_type_id(std::string name);
  static char* get_type_name(unsigned id);

  static unsigned int assign_transaction_id();
  static void tlm2_turn_off_transaction_mapping(const std::string & port_name, 
                                                const std::string & export_name);

  static bool reset_detected();

  static void report_sc_error(const char * const message, const char * const submessage);
  static void print_sc_report(const sc_report& ex);

  // Connection-related stuff

  static uvm_ml_tlm_conn_info* get_or_create_conn_info(std::string name);
  static uvm_ml_tlm_conn_info* get_conn_info(std::string name); 
  static uvm_ml_tlm_conn_info* get_conn_info(unsigned id); 
  static void add_transrec_to_map(sc_object* obj, uvm_ml_tlm_transrec_base* tr);
  static uvm_ml_tlm_transrec_base* get_transrec(sc_object* obj);
  static void add_socket(std::string s, ml_tlm2_connector_base* conn);
  static unsigned find_socket_id(std::string s);
  static bool is_tlm2_connector(unsigned connector_id);
  static ml_tlm2_connector_base*  get_ml_tlm2_connector_base(unsigned target_connector_id);

  static void                     add_parent_proxy(parent_component_proxy * proxy,
                                                   int                      parent_framework_id,
                                                   int                      parent_junction_node_id);
  static parent_component_proxy * find_parent_proxy_by_id(int parent_junction_node_id);

  static bool                  quasi_static_elaboration_started() { return m_quasi_static_elaboration_started; }
  static void                  set_quasi_static_end_of_construction() { m_quasi_static_end_of_construction = true; }
  static bool                  quasi_static_construction_ended() { return m_quasi_static_end_of_construction; }

  static bool                  is_tree_node_quasi_static(unsigned root_node_id);
  static sc_module *           get_quasi_static_tree_node_by_id(unsigned node_id);
  static unsigned int          add_quasi_static_tree_node(sc_module * pmod);

  static parent_component_proxy * create_parent_proxy_with_helpers(sc_module *    parent_helper,
                                                                   const string & path);

protected:

  static bool m_quasi_static_elaboration_started;
  static bool m_quasi_static_end_of_construction;

  static sc_strhash<uvm_ml_tlm_conn_info*>* conn_info_by_name;
  static std::map<unsigned,uvm_ml_tlm_conn_info*>* conn_info_by_id;
  static std::map<sc_object*, uvm_ml_tlm_transrec_base*>* obj_transrec_map;
  static std::map<std::string, unsigned>* socket_map;
  static std::map<unsigned, ml_tlm2_connector_base*>* connector_map;
  static unsigned m_nextid;

  static vector<string>                                                    static_top_names;
  static vector<sc_module *>                                               quasi_static_tree_nodes;
    
  static map<int /* parent junction node id */, parent_component_proxy *>  parent_proxies;

private:
  static unsigned get_next_top_id() { return static_top_names.size() + quasi_static_tree_nodes.size(); }
};

/*! \class uvm_ml_tlm_receiver_base
  \brief Base class for ML TLM receiver interface.

  
*/
class uvm_ml_tlm_receiver_base : public uvm_ml_tlm_transrec_base {
public:
  uvm_ml_tlm_receiver_base(const char* name_);
  virtual ~uvm_ml_tlm_receiver_base();
  virtual bool is_transmitter() const;
  virtual void bind_export(sc_core::sc_export_base* b);
  virtual sc_core::sc_interface* get_interface() const;
  //
protected:
  sc_core::sc_interface* m_iface;
public:
  void umsg(std::string f) {
        char msg[1024];
        sprintf(msg,"uvm function not implemented by receiver: %s",f.c_str());
        uvm_ml_utils::report_sc_error(UVM_RECEIVER_FUNC_NOT_IMPL_,msg);
    }
  virtual unsigned put_bitstream(
    unsigned stream_size, 
    void * stream  ) { umsg("put_bitstream"); return 0; }
  virtual void put_bitstream_request(
    unsigned call_id, 
    unsigned stream_size, 
    void * stream
  ) { umsg("put_bitstream_request"); }
  virtual int try_put_bitstream(
    unsigned stream_size , 
    void * stream
  ) { umsg("try_put_bitstream"); return 0; } 
  virtual int can_put() { umsg("can_put"); return 0; } 
  //
  virtual unsigned get_bitstream(
    unsigned* stream_size , 
    void * stream
  ) { umsg("get_bitstream"); return 0; } 
  virtual void get_bitstream_request(
    unsigned call_id
  ) { umsg("get_bitstream_request"); } 
  virtual int try_get_bitstream(
    unsigned * stream_size_ptr,
    void * stream
  ) { umsg("try_get_bitstream"); return 0; } 
  virtual int can_get() { umsg("can_get"); return 0; } 
  //
  virtual unsigned peek_bitstream(
    unsigned * stream_size_ptr,
    void * stream
  ) { umsg("peek_bitstream"); return 0; } 
  virtual void peek_bitstream_request(
    unsigned call_id
  ) { umsg("peek_bitstream_request"); } 
  virtual int try_peek_bitstream(
    unsigned * stream_size_ptr,
    void * stream
  ) { umsg("try_peek_bitstream"); return 0; } 
  virtual int can_peek() { umsg("can_peek"); return 0; } 
  //
  virtual unsigned transport_bitstream(
    unsigned req_stream_size, 
    void * req_stream,
    unsigned* rsp_stream_size,
    void* rsp_stream
  ) { umsg("transport_bitstream"); return 0; }
  virtual void transport_bitstream_request(
    unsigned call_id, 
    unsigned req_stream_size, 
    void * req_stream,
    unsigned* rsp_stream_size,
    void* rsp_stream
  ) { umsg("transport_bitstream_request"); }
  virtual void write_bitstream(
    unsigned stream_size , 
    void * stream
  ) { umsg("write_bitstream"); return; } 
};

/////////////////

/*! \class uvm_ml_tlm_transmitter
  \brief Catch transmitter of unsupported interface.

  generate compilation error
*/
template <class IF> class uvm_ml_tlm_transmitter :
  public uvm_ml_tlm_transmitter_base, virtual public IF {
public:
  // If you get here it won't compile
};

/*! \class uvm_ml_tlm_receiver
  \brief Catch receiver of unsupported interface.

  generate compilation error
*/
template <class IF> class uvm_ml_tlm_receiver :
  public uvm_ml_tlm_receiver_base, virtual public IF {
public:
  // If you get here it won't compile
};

/////////////////

/*! \class uvm_ml_tlm_transmitter_tlm
  \brief Templated class for ML TLM1 transmitter interface.

  Templated by the sent and received types
*/
template <typename T1, typename T2>
class uvm_ml_tlm_transmitter_tlm :
  virtual public uvm_ml_tlm_transmitter_base,
  virtual public tlm::tlm_master_if<T1,T2>,
  virtual public tlm::tlm_slave_if<T2,T1>
//#ifdef __TLM_ANALYSIS_H__
#if !defined(NC_SYSTEMC) || defined(__TLM_ANALYSIS_H__)
  ,virtual public tlm::tlm_analysis_if<T1>
#endif
{
public:
  uvm_ml_tlm_transmitter_tlm(const char* name_) 
#ifdef NC_SYSTEMC
    : uvm_ml_tlm_transmitter_base(name_), dummy_event("sync", false) 
#else
    : uvm_ml_tlm_transmitter_base(name_), dummy_event()
#endif 
  {}
  ~uvm_ml_tlm_transmitter_tlm() { }
  virtual std::string interface_name() { return "tlm"; } // object->if_name()???
  unsigned connId;
  unsigned adapterId;

  // the put family

  virtual void put( const T1 &t ) {
    if (!this->id_is_valid()) { this->unconnected_error(); return; }
    // blocking call, need to use mlupo from pool
    uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_packer_pack(t,v);
    unsigned connId = this->connection_id();
    uvm_ml_tlm_trans::request_put(
      connId, v
    );
    uvm_ml_utils::release_mlupo_to_pool(v);
  }

  virtual bool nb_put( const T1 &t ) { 
    if (!this->id_is_valid()) { this->unconnected_error(); return false; }
    uvm_ml_packed_obj& v = uvm_ml_utils::get_static_mlupo();
    uvm_ml_packer_pack(t,&v);
    unsigned connId = this->connection_id();
    int ret = uvm_ml_tlm_trans::nb_put(
      connId, &v
    );
    return (ret == 0) ? false : true;
  }

  virtual bool nb_can_put( tlm::tlm_tag<T1> *t = 0 ) const { 
    if (!this->id_is_valid()) { this->unconnected_error(); return false; }
    unsigned connId = this->connection_id();
    int ret = uvm_ml_tlm_trans::can_put(connId);
    return (ret == 0) ? false : true;
  }

  virtual const sc_event &ok_to_put( tlm::tlm_tag<T1> *t = 0 ) const 
  {
      char msg[1024];
      sprintf(msg, "\nTLM interface is 'ok_to_put' \n");
        uvm_ml_utils::report_sc_error(ML_UVM_UNIMPLEMENTED_INTERFACE_, msg);
        return dummy_event;
  }
  // the get family

  virtual T2 get( tlm::tlm_tag<T2> *tag = 0 ) {
    if (!this->id_is_valid()) { this->unconnected_error(); return T2(); }
    // blocking call, need to use mlupo from pool
    uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::allocate_mlupo(v);
    unsigned connId = this->connection_id();
    uvm_ml_tlm_trans::request_get(
      connId, v
    );
    T2* t;
    uvm_ml_packer_unpack_create(v, t, t);
    T2 tt = *t;
    delete t;
    uvm_ml_utils::release_mlupo_to_pool(v);
    return tt;
  }

  virtual bool nb_get( T2 &t ) { 
    if (!this->id_is_valid()) { this->unconnected_error(); return false; }

    uvm_ml_packed_obj& v = uvm_ml_utils::get_static_mlupo();
    uvm_ml_utils::allocate_mlupo(&v);
    unsigned connId = this->connection_id();
    int ret = uvm_ml_tlm_trans::nb_get(
      connId, &v
    );
    if (ret == 0) {
      // do not touch the input argument
      return false;
    }
    T2* t1;
    uvm_ml_packer_unpack_create(&v, t1, t1);
    t = *t1;
    delete t1;
    return true;
  }

  virtual bool nb_can_get( tlm::tlm_tag<T2> *t = 0 ) const { 
    if (!this->id_is_valid()) { this->unconnected_error(); return false; }
    unsigned connId = this->connection_id();
    int ret = uvm_ml_tlm_trans::can_get(connId);
    return (ret == 0) ? false : true;
  }

  virtual const sc_event &ok_to_get( tlm::tlm_tag<T2> *t = 0 ) const
  {
      char msg[1024];
      sprintf(msg, "\nTLM interface is 'ok_to_get' \n");
      uvm_ml_utils::report_sc_error(ML_UVM_UNIMPLEMENTED_INTERFACE_, msg);
      return dummy_event;
  }
  // the peek family

  virtual T2 peek( tlm::tlm_tag<T2> *tag = 0 ) const { 
    if (!this->id_is_valid()) { this->unconnected_error(); return T2(); }
    // blocking call, need to use mlupo from pool
    uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::allocate_mlupo(v);
    unsigned connId = this->connection_id();
    uvm_ml_tlm_trans::request_peek(
      connId, v
    );
    T2* t;
    uvm_ml_packer_unpack_create(v, t, t);
    T2 tt = *t;
    delete t;
    uvm_ml_utils::release_mlupo_to_pool(v);
    return tt;
  }

  virtual bool nb_peek( T2 &t ) const { 
    if (!this->id_is_valid()) { this->unconnected_error(); return false; }

    uvm_ml_packed_obj& v = uvm_ml_utils::get_static_mlupo();
    uvm_ml_utils::allocate_mlupo(&v);
    unsigned connId = this->connection_id();
    int ret = uvm_ml_tlm_trans::nb_peek(
      connId, &v
    );
    if (ret == 0) {
      // do not touch the input argument
      return false;
    }
    T2* t1;
    uvm_ml_packer_unpack_create(&v, t1, t1);
    t = *t1;
    delete t1;
    return true;
  }

  virtual bool nb_can_peek( tlm::tlm_tag<T2> *t = 0 ) const { 
    if (!this->id_is_valid()) { this->unconnected_error(); return false; }
    unsigned connId = this->connection_id();
    int ret = uvm_ml_tlm_trans::can_peek(connId);
    return (ret == 0) ? false : true;
  }

  virtual const sc_event &ok_to_peek( tlm::tlm_tag<T2> *t = 0 ) const {
      char msg[1024];
      sprintf(msg, "\nTLM interface is 'ok_to_peek' \n");
      uvm_ml_utils::report_sc_error(ML_UVM_UNIMPLEMENTED_INTERFACE_, msg);
      return dummy_event;
  }

  // analysis_if

  virtual void write( const T1 &t ) { 
    if (!this->id_is_valid()) { this->unconnected_error(); return; }

    uvm_ml_packed_obj& v = uvm_ml_utils::get_static_mlupo();
    uvm_ml_packer_pack(t,&v);
    unsigned connId = this->connection_id();
    uvm_ml_tlm_trans::write(
      connId, &v
    );
  }

protected:
  sc_event dummy_event;
};

/*! \class uvm_ml_tlm_transmitter_tlm_transport
  \brief Templated class for ML TLM1 transport interface.

  templated by the request and response types
*/
template <typename REQ, typename RSP>
class uvm_ml_tlm_transmitter_tlm_transport :
  virtual public uvm_ml_tlm_transmitter_base,
  virtual public tlm::tlm_transport_if<REQ,RSP>
{
public:
  uvm_ml_tlm_transmitter_tlm_transport(const char* name_) 
    : uvm_ml_tlm_transmitter_base(name_) { 
  }
  ~uvm_ml_tlm_transmitter_tlm_transport() { }
  virtual std::string interface_name() { return "tlm"; } // object->if_name()???
  unsigned connId;
  unsigned adapterId;
  //
  virtual RSP transport( const REQ &t ) { 
    if (!this->id_is_valid()) { this->unconnected_error(); return RSP(); }
    //uvm_ml_packed_obj req, rsp;
    // blocking call, need to use mlupo from pool
    uvm_ml_packed_obj* req = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_packed_obj* rsp = uvm_ml_utils::get_mlupo_from_pool();
    uvm_ml_utils::allocate_mlupo(rsp);
    uvm_ml_packer_pack(t,req);
    unsigned connId = this->connection_id();
    uvm_ml_tlm_trans::request_transport(
      connId, req, rsp
    );
    RSP* t1;
    uvm_ml_packer_unpack_create(rsp, t1, t1);
    RSP tt = *t1;
    delete t1;
    uvm_ml_utils::release_mlupo_to_pool(req);
    uvm_ml_utils::release_mlupo_to_pool(rsp);
    return tt;
  }
};

////////////

/*! \class uvm_ml_tlm_receiver_tlm
  \brief Templated class for ML TLM1 receiver interface.

  Templated by the sent and received types
*/
template <typename T1, typename T2> class uvm_ml_tlm_receiver_tlm
    : public uvm_ml_tlm_receiver_base
{
public:


  uvm_ml_tlm_receiver_tlm(const char* nm) 
    : uvm_ml_tlm_receiver_base(nm) { m_init_done = false; }
  ~uvm_ml_tlm_receiver_tlm() { } 
  void init_interfaces() {
    if (m_init_done) return;
    iface_put = DCAST<tlm::tlm_blocking_put_if<T1>*>(get_interface());
    iface_get = DCAST<tlm::tlm_blocking_get_if<T2>*>(get_interface());
    iface_peek = DCAST<tlm::tlm_blocking_peek_if<T2>*>(get_interface());
    iface_nb_put = DCAST<tlm::tlm_nonblocking_put_if<T1>*>(get_interface());
    iface_nb_get = DCAST<tlm::tlm_nonblocking_get_if<T2>*>(get_interface());
    iface_nb_peek = DCAST<tlm::tlm_nonblocking_peek_if<T2>*>(get_interface());
    iface_transport = DCAST<tlm::tlm_transport_if<T1,T2>*>(get_interface());
//#ifdef __TLM_ANALYSIS_H__
#if !defined(NC_SYSTEMC) || defined(__TLM_ANALYSIS_H__)
    iface_analysis = DCAST<tlm::tlm_analysis_if<T1>*>(get_interface());
#endif
    m_init_done = true;
  }
  unsigned put_bitstream(
    unsigned stream_size, 
    void * stream
                         ){ 
    init_interfaces();
    if (!iface_put) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T1* t;
    //
    //uvm_ml_packed_obj vt; 
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,stream_size,stream);
    //
    uvm_ml_packer_unpack_create(&vt, t, t);
    iface_put->put(*t);
    delete t;
    return 0;
  } 
#define UMSGU(f) \
  { \
  char msg[1024]; \
  sprintf(msg,"uvm function not implemented by receiver: %s",#f); \
  uvm_ml_utils::report_sc_error(UVM_RECEIVER_FUNC_NOT_IMPL_,msg);	  \
  }

  void put_bitstream_request(
    unsigned call_id, 
    unsigned stream_size, 
    void * stream
                             ) { 
    UMSGU(put_bitstream_request); 
  } 

  int try_put_bitstream(
    unsigned stream_size , 
    void * stream
  ){ 
    init_interfaces();
    if (!iface_nb_put) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T1* t;
    //
    //uvm_ml_packed_obj vt; 
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,stream_size,stream);
    //
    uvm_ml_packer_unpack_create(&vt, t, t);
    int i = iface_nb_put->nb_put(*t);
    delete t;
    return i;
  }
  int can_put()  {
    init_interfaces();
    if (!iface_nb_put) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    int i = iface_nb_put->nb_can_put();
    return i;
  }
  //
  unsigned get_bitstream(
    unsigned* stream_size,
    void * stream
  ) { 
    init_interfaces();
    if (!iface_get) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T2 t;
    t = iface_get->get();

    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_packer_pack(t,&vt);
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, stream);
    return 0; // ???
  }

  void get_bitstream_request(
    unsigned call_id
                             ) { UMSGU(get_bitstream_request); } 
  int try_get_bitstream(
    unsigned * stream_size,
    void * stream
    )  { 
    init_interfaces();
    if (!iface_nb_get) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T2 t;
    bool b = iface_nb_get->nb_get(t);

    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_packer_pack(t,&vt);
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, stream);
    return b; 
  }

  int can_get()  { 
    init_interfaces();
    if (!iface_nb_get) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T2 t;
    //
    bool b = iface_nb_get->nb_can_get();
    return b ? 1 : 0;
  }

  //
  unsigned peek_bitstream(
    unsigned* stream_size,
    void * stream
    ) { 
    init_interfaces();
    if (!iface_peek) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,""); 
        return 0; 
    }
    T2 t;
    //
    t = iface_peek->peek();

    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_packer_pack(t,&vt);
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, stream);
    return 0; // ???
  } 
  void peek_bitstream_request(
    unsigned call_id
  ) { UMSGU(peek_bitstream_request); } 
  int try_peek_bitstream(
    unsigned * stream_size,
    void * stream
  ) { 
    init_interfaces();
    if (!iface_nb_peek) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T2 t;

    bool b = iface_nb_peek->nb_peek(t);

    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_packer_pack(t,&vt);
    *stream_size = uvm_ml_utils::copy_from_mlupo(vt, stream);
    return b; 
  }

  int can_peek()  { 
    init_interfaces();
    if (!iface_nb_peek) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T2 t;
    //
    bool b = iface_nb_peek->nb_can_peek();
    return b ? 1 : 0;
  }
  //
  virtual unsigned transport_bitstream( 
    unsigned req_stream_size,
    void* req_stream,
    unsigned* rsp_stream_size,
    void* rsp_stream
    ) {
    init_interfaces();
    if (!iface_transport) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
      return 0; 
    }
    T1* t1;

    uvm_ml_packed_obj& vt1 = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt1,req_stream_size,req_stream);
    //
    uvm_ml_packer_unpack_create(&vt1, t1, t1);
    //
    T2 t2;
    t2 = iface_transport->transport(*t1);
    delete t1;
    //
    //
    uvm_ml_packed_obj& vt2 = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_packer_pack(t2,&vt2);
    *rsp_stream_size = uvm_ml_utils::copy_from_mlupo(vt2, rsp_stream);
    return 0;
  }

  //
  void write_bitstream(
    unsigned stream_size , 
    void * stream
                       )  { 
#if (! defined(NC_SYSTEMC) || defined(__TLM_ANALYSIS_H__))
    init_interfaces();
    if (!iface_analysis) { 
        uvm_ml_utils::report_sc_error(UVM_PORT_IFACE_,"");
        
      return; 
    }
    T1* t;
    //
    uvm_ml_packed_obj& vt = uvm_ml_utils::get_static_mlupo(); 
    uvm_ml_utils::fill_mlupo(vt,stream_size,stream);
    //
    uvm_ml_packer_unpack_create(&vt, t, t);
    iface_analysis->write(*t);
    delete t;
#endif
  }
protected:
  bool m_init_done;
  tlm::tlm_blocking_put_if<T1>* iface_put;
  tlm::tlm_nonblocking_put_if<T1>* iface_nb_put;
  tlm::tlm_blocking_get_if<T2>* iface_get;
  tlm::tlm_nonblocking_get_if<T2>* iface_nb_get;
  tlm::tlm_blocking_peek_if<T2>* iface_peek;
  tlm::tlm_nonblocking_peek_if<T2>* iface_nb_peek;
  tlm::tlm_transport_if<T1,T2>* iface_transport;
//#ifdef __TLM_ANALYSIS_H__
#if !defined(NC_SYSTEMC) || defined(__TLM_ANALYSIS_H__)
  tlm::tlm_analysis_if<T1>* iface_analysis;
#endif
};

/////////////////
#define uvm_ml_tlm_declare_register_internal(IF) \
template <typename T, int N, sc_core::sc_port_policy POL> \
void uvm_ml_register_internal( \
  sc_core::sc_port<tlm::IF<T>,N,POL>* p \
) { \
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;     \
  std::string s = std::string(p->basename()) + "_trans"; \
  uvm_ml_tlm_transmitter_tlm<T,T>* trans = \
    new uvm_ml_tlm_transmitter_tlm<T,T>(s.c_str()); \
  p->bind(*trans); \
  trans->object(p); \
  trans->set_intf_name(#IF); \
  trans->set_REQ_name(T().get_type_name()); \
  trans->set_RSP_name(T().get_type_name()); \
} \
 \
template <typename T> \
void uvm_ml_register_internal( \
  sc_core::sc_export<tlm::IF<T> >* p \
) { \
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;     \
  std::string s = std::string(p->basename()) + "_rec"; \
  uvm_ml_tlm_receiver_tlm<T,T>* rec =  \
    new uvm_ml_tlm_receiver_tlm<T,T>(s.c_str()); \
  rec->bind_export(p); \
  rec->set_intf_name(#IF); \
  rec->set_REQ_name(T().get_type_name()); \
  rec->set_RSP_name(T().get_type_name()); \
}
uvm_ml_tlm_declare_register_internal(tlm_blocking_put_if)
uvm_ml_tlm_declare_register_internal(tlm_nonblocking_put_if)
uvm_ml_tlm_declare_register_internal(tlm_put_if)

uvm_ml_tlm_declare_register_internal(tlm_blocking_get_if)
uvm_ml_tlm_declare_register_internal(tlm_nonblocking_get_if)
uvm_ml_tlm_declare_register_internal(tlm_get_if)

uvm_ml_tlm_declare_register_internal(tlm_blocking_peek_if)
uvm_ml_tlm_declare_register_internal(tlm_nonblocking_peek_if)
uvm_ml_tlm_declare_register_internal(tlm_peek_if)

uvm_ml_tlm_declare_register_internal(tlm_blocking_get_peek_if)
uvm_ml_tlm_declare_register_internal(tlm_nonblocking_get_peek_if)
uvm_ml_tlm_declare_register_internal(tlm_get_peek_if)

//#ifdef __TLM_ANALYSIS_H__
#if !defined(NC_SYSTEMC) || defined(__TLM_ANALYSIS_H__)

template <typename T, int N, sc_core::sc_port_policy POL> 
void uvm_ml_register_internal( 
  sc_core::sc_port<tlm::tlm_analysis_if<T>,N,POL>* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;     
  std::string s = std::string(p->basename()) + "_trans"; 
  uvm_ml_tlm_transmitter_tlm<T,T>* trans = 
    new uvm_ml_tlm_transmitter_tlm<T,T>(s.c_str()); 
  p->bind(*trans); 
  trans->object(p); 
  trans->set_intf_name("tlm_analysis_if"); 
  trans->set_REQ_name(T().get_type_name()); 
  trans->set_RSP_name(T().get_type_name()); 
} 

template <typename T> 
void uvm_ml_register_internal( 
  tlm::tlm_analysis_port<T>* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;     
  std::string s = std::string(p->basename()) + "_trans"; 
  uvm_ml_tlm_transmitter_tlm<T,T>* trans = 
    new uvm_ml_tlm_transmitter_tlm<T,T>(s.c_str()); 
  p->bind(*trans); 
  trans->object(p); 
  trans->set_intf_name("tlm_analysis_if"); 
  trans->set_REQ_name(T().get_type_name()); 
  trans->set_RSP_name(T().get_type_name()); 
} 

template <typename T> 
void uvm_ml_register_internal( 
  sc_core::sc_export<tlm::tlm_analysis_if<T> >* p 
) { 
  if (uvm_ml::uvm_ml_utils::reset_detected()) return;     
  std::string s = std::string(p->basename()) + "_rec"; 
  uvm_ml_tlm_receiver_tlm<T,T>* rec =  
    new uvm_ml_tlm_receiver_tlm<T,T>(s.c_str()); 
  rec->bind_export(p); 
  rec->set_intf_name("tlm_analysis_if"); 
  rec->set_REQ_name(T().get_type_name()); 
  rec->set_RSP_name(T().get_type_name()); 
}

#endif

} // namespace uvm_ml

#endif
