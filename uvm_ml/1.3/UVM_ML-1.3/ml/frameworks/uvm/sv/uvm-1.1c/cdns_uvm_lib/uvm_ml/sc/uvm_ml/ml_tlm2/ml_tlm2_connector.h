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

/*! \file ml_tlm2_connector.h
  \brief Implementation of TLM2 connectors.
*/
#ifndef _ML_TLM2_CONNECTOR_H_
#define _ML_TLM2_CONNECTOR_H_

#include <typeinfo>
#include "systemc.h"
#include "tlm.h"
#include "uvm.h"
#include "common/uvm_ml_packer.h"

using namespace std;
using namespace tlm;
using namespace uvm_ml;

/*! \struct ml_tlm2_delay_val
  \brief Pairs of value and time unit.

  
*/
struct ml_tlm2_delay_val {
  sc_time_unit tu;
  int delay_value;
};

/*! \class ml_tlm2_time_params
  \brief Convert time parameters.

  Convertion methods between sc_time used in SC and {unit,value} used in SV/e
*/
class ml_tlm2_time_params {
 public:
  ml_tlm2_time_params() {};
  ml_tlm2_delay_val get_delay_struct(sc_time& delay) {
    static bool first = true;
    static sc_time_unit tu = SC_PS;
    static int mult;
    ml_tlm2_delay_val d;
    if(first) {
      first = false;
      if(sc_get_time_resolution() == sc_time(1, SC_FS)) {tu = SC_FS; mult = 1;};
      if(sc_get_time_resolution() == sc_time(10, SC_FS)) {tu = SC_FS; mult = 10;};
      if(sc_get_time_resolution() == sc_time(100, SC_FS)) {tu = SC_FS; mult = 100;};
      if(sc_get_time_resolution() == sc_time(1, SC_PS)) {tu = SC_PS; mult = 1;};
      if(sc_get_time_resolution() == sc_time(10, SC_PS)) {tu = SC_PS; mult = 10;};
      if(sc_get_time_resolution() == sc_time(100, SC_PS)) {tu = SC_PS; mult = 100;};
      if(sc_get_time_resolution() == sc_time(1, SC_NS)) {tu = SC_NS; mult = 1;};
      if(sc_get_time_resolution() == sc_time(10, SC_NS)) {tu = SC_NS; mult = 10;};
      if(sc_get_time_resolution() == sc_time(100, SC_NS)) {tu = SC_NS; mult = 100;};
      if(sc_get_time_resolution() == sc_time(1, SC_US)) {tu = SC_US; mult = 1;};
      if(sc_get_time_resolution() == sc_time(10, SC_US)) {tu = SC_US; mult = 10;};
      if(sc_get_time_resolution() == sc_time(100, SC_US)) {tu = SC_US; mult = 100;};
      if(sc_get_time_resolution() == sc_time(1, SC_MS)) {tu = SC_MS; mult = 1;};
      if(sc_get_time_resolution() == sc_time(10, SC_MS)) {tu = SC_MS; mult = 10;};
      if(sc_get_time_resolution() == sc_time(100, SC_MS)) {tu = SC_MS; mult = 100;};
      if(sc_get_time_resolution() == sc_time(1, SC_SEC)){tu = SC_SEC; mult = 1;};
      if(sc_get_time_resolution() == sc_time(10, SC_SEC)){tu = SC_SEC; mult = 10;};
      if(sc_get_time_resolution() == sc_time(100, SC_SEC)){tu = SC_SEC; mult = 100;};
    }
    d.tu = tu;
    d.delay_value = mult*delay.value();
    return d;
  }
};

static ml_tlm2_time_params* global_tp = new ml_tlm2_time_params;

#ifndef ML_TLM2_UNINITIALIZED_ID
#define ML_TLM2_UNINITIALIZED_ID 0xffffffff
#endif

namespace uvm_ml {

typedef enum  {
  ML_TLM2_PACK_OP,
  ML_TLM2_UNPACK_OP,
  ML_TLM2_COPY_OP,
  ML_TLM2_DELETE_OP,
  ML_TLM2_BW_UPDATE_OP
} ml_tlm2_oper;

  // transaction mapping
  tlm_generic_payload *ml_tlm2_get_transaction_by_id(unsigned int id);
  bool ml_tlm2_transaction_mapping_disabled(const std::string &socket_name);
  void ml_tlm2_transaction_mapping_mm_error(const string &socket_name);
  void ml_tlm2_transaction_mapping_update_error(const string &socket_name, 
						const string &intf_name, 
						tlm_phase phase);
  void ml_tlm2_transaction_mapping_remove_error(const string &socket_name, 
						const string &intf_name, 
						tlm_phase phase, 
						tlm_sync_enum status);
// transaction mapping methods
void         ml_tlm2_map_transaction(tlm_generic_payload * trans, unsigned int & transaction_id);
unsigned int ml_tlm2_get_id_by_transaction(tlm_generic_payload &trans);
bool         ml_tlm2_release_transaction(tlm_generic_payload * trans, unsigned int & transaction_id);
					  
void         ml_tlm2_pack(tlm_generic_payload & val, uvm_ml_packed_obj* p);
void         ml_tlm2_unpack_create(uvm_ml_packed_obj* p, tlm_generic_payload*& val);
void         ml_tlm2_bw_update_gp(tlm_generic_payload & tlm_gp, tlm_generic_payload & other);

void         ml_tlm2_update_data_from_response(tlm_generic_payload &trans, 
			                       tlm_generic_payload &response_gp,
			                       string full_socket_name);

void ml_tlm2_do_register_initiator(const std::string &initiator_socket_name, 
                                   const std::string &transactor_name);
void ml_tlm2_do_register_target(const std::string &target_socket_name, 
                                const std::string &transactor_name);
/*! \class ml_tlm2_connector_base
  \brief Base class for TLM2 connectors.

  Provides method for registering the socket name
*/
class ml_tlm2_connector_base: public sc_module
{
  public :

    void register_top_of_the_socket_name(const string & sname);

  public:
    unsigned int conn_id;
    bool is_target;
}; // class ml_tlm2_connector_base


/*! \class ml_tlm2_target_connector_base
  \brief Base class for TLM2 target connector.

  Adds the virtual methods for target connectors
*/
class ml_tlm2_target_connector_base: public ml_tlm2_connector_base
{
 public :
  virtual void b_transport(uvm_ml_packed_obj& vt, sc_time_unit *delay_unit, double *delay_value, sc_time_unit time_unit, double time_value) = 0;
  virtual tlm_sync_enum  nb_transport_fw(uvm_ml_packed_obj& vt, tlm_phase_enum *phase, unsigned int transaction_id, sc_time_unit *delay_unit, double *delay_value, sc_time_unit time_unit, double time_value) = 0;
  virtual unsigned transport_dbg(uvm_ml_packed_obj& vt, sc_time_unit time_unit, double time_value) = 0;
};


/*! \class ml_tlm2_initiator_connector_base
  \brief Base class for TLM2 initiator connector.

  Adds the virtual methods for initiator connectors
*/
class ml_tlm2_initiator_connector_base: public ml_tlm2_connector_base
{
 public :
  virtual tlm_sync_enum nb_transport_bw(uvm_ml_packed_obj& vt, tlm_phase_enum *phase, unsigned int transaction_id, sc_time_unit *delay_unit, double *delay_value, sc_time_unit time_unit, double time_value) = 0;
};

} // namespace uvm_ml


// Target connector 
// adapter for propagating transactions from testbench to SC target
/*! \class ml_tlm2_target_connector
  \brief Template of TLM2 target connector.

  Templated by type of the transaction, the bus width and protocol types
  Implements the methods and tasks needed for ML TLM2 communication 
*/
template <class REQ, unsigned int BUSWIDTH, typename TYPES = tlm::tlm_base_protocol_types>
class ml_tlm2_target_connector: public ml_tlm2_target_connector_base
  ,virtual public tlm::tlm_bw_transport_if<TYPES>
  {
    public :
    typedef typename TYPES::tlm_payload_type transaction_type;
    tlm::tlm_initiator_socket<BUSWIDTH, TYPES> isocket;
    
    // transaction mapping for nb calls
    bool disable_transaction_mapping;
    bool disable_transaction_mapping_set;
    std::string m_socket_name;

    // constructor
    ml_tlm2_target_connector(sc_module_name name_, tlm_target_socket<BUSWIDTH,TYPES> &s, std::string sname) :
    isocket("isocket"),
    disable_transaction_mapping(false),
    disable_transaction_mapping_set(false),
    m_socket_name(sname)
    {
      isocket(*this);
      isocket(s);
      is_target = true; 
      register_top_of_the_socket_name(sname);
      ml_tlm2_do_register_target(sname,name());
      uvm_ml_utils::add_socket(sname, this);
    }
    
    void b_transport(uvm_ml_packed_obj& vt, sc_time_unit *delay_unit, double *delay_value, sc_time_unit time_unit, double time_value) {
      tlm_generic_payload * tlm_gp = 0;

      sc_time delay = sc_time(*delay_value, (sc_time_unit)*delay_unit);

      ml_tlm2_unpack_create(&vt, tlm_gp);

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)tlm_gp;

      // Hold the generic_payload until transaction is completed
      //assert(tx->has_mm());
      if(!tx->has_mm()) {
	UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: b_transport failed because the transaction has no memory manager","");
	return;
      };
      tx->acquire();

      // send a TLM2 transaction to the DUT
      isocket->b_transport(*(dynamic_cast<REQ *>(tx)), delay);

      // Reconstruct delay
      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(delay);
      *delay_value= delay_struct.delay_value;
      *delay_unit = (sc_time_unit)delay_struct.tu;

      // Pack into ml packed object
      ml_tlm2_pack(*tlm_gp, &vt);

      tx->release();
    }

    tlm_sync_enum nb_transport_fw(uvm_ml_packed_obj& vt, tlm_phase_enum *phase, unsigned int transaction_id, sc_time_unit *delay_unit, double *delay_value, sc_time_unit time_unit, double time_value) {
      tlm_generic_payload * tlm_gp = 0;

      sc_time delay = sc_time(*delay_value, (sc_time_unit)*delay_unit);
      tlm_phase fw_phase(*phase);

      ml_tlm2_unpack_create(&vt, tlm_gp);

      // map the transaction if needed
      set_transaction_mapping();
      if (disable_transaction_mapping == false) {
	if (*phase == BEGIN_REQ) {
	  //assert (transaction_id != ML_TLM2_UNINITIALIZED_ID);
	  if(transaction_id == ML_TLM2_UNINITIALIZED_ID) {
	    UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: nb_transport_fw failed due to uninitialized transaction","");
	    return TLM_COMPLETED;
	  };
	  ml_tlm2_map_transaction(tlm_gp, transaction_id);
	} else if (*phase == END_RESP) {
	  // retrieve the original gp sent on the forward path
	  transaction_type *mapped_trans = 
	    dynamic_cast<transaction_type*>(ml_tlm2_get_transaction_by_id(transaction_id));
	  if (!mapped_trans) {
	    ml_tlm2_transaction_mapping_update_error(m_socket_name,"nb_transport_fw",*phase);
	  }
	  // set the original gp in the current request. no fields are updated
	  tlm_gp = mapped_trans; 
	}
      }

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)tlm_gp;

      // Hold the generic_payload until transaction is completed
      //assert(tx->has_mm());
      if(!(tx->has_mm())) {
	UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: nb_transport_fw failed because the transaction has no memory manager","");
	return TLM_COMPLETED;
      };
      tx->acquire();

      // send a TLM2 transaction to the DUT
      tlm_sync_enum ret = isocket->nb_transport_fw(*(dynamic_cast<REQ *>(tx)), fw_phase, delay);

      *phase = (tlm_phase_enum)((unsigned int)fw_phase);

      // Reconstruct delay
      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(delay);
      *delay_value= delay_struct.delay_value;
      *delay_unit = (sc_time_unit)delay_struct.tu;

      // release mapped transaction
      if (disable_transaction_mapping == false) { 
	if (*phase == END_RESP || ret == TLM_COMPLETED) {
	  bool result = ml_tlm2_release_transaction(tlm_gp, transaction_id);
	  if (!result) {
	    ml_tlm2_transaction_mapping_remove_error(m_socket_name,"nb_transport_fw",*phase,ret);
	  }		
	}
      }

      // Pack into ml packed object
      ml_tlm2_pack(*tlm_gp, &vt);
      
      if(tx->get_ref_count() != 0) {
	tx->release();      
      };

      return ret;
    }

    tlm_sync_enum nb_transport_bw(REQ& trans, tlm_phase& phase, sc_time& delay)
    {
      sc_time_unit time_unit;
      double       time_value;
      sc_time_unit delay_unit;
      double       delay_value;
      unsigned int transaction_id = ML_TLM2_UNINITIALIZED_ID;
      tlm_generic_payload * t1 = 0;

      uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
      uvm_ml_utils::allocate_mlupo(v);

      // copy original transaction id to outgoing transaction
      set_transaction_mapping();
      if (disable_transaction_mapping == false) {
	transaction_id = ml_tlm2_get_id_by_transaction(trans);
	if (transaction_id == ML_TLM2_UNINITIALIZED_ID) {
	  ml_tlm2_transaction_mapping_update_error(m_socket_name,"nb_transport_bw",phase);
	}
      }

      // Pack to ml packed object
      ml_tlm2_pack(trans, v);

      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(delay);
      delay_value = delay_struct.delay_value;
      delay_unit = (sc_time_unit)delay_struct.tu;
      tlm_phase_enum phase_id = (tlm_phase_enum) (unsigned int) phase;

      sc_time ct = sc_time_stamp();
      delay_struct = global_tp->get_delay_struct(ct);
      time_value= delay_struct.delay_value;
      time_unit = (sc_time_unit)delay_struct.tu;

      // Call testbench
      tlm_sync_enum ret = (tlm_sync_enum) uvm_ml_tlm_trans::tlm2_nb_transport_bw(conn_id, 
											     v, 
										             (unsigned int *)&phase_id,
                                                                                             transaction_id,
											     &delay_unit, 
											     &delay_value
                                                                                             );

      // update delay and phase
      delay = sc_time(delay_value, (sc_time_unit)(delay_unit));
      phase = phase_id;

      // Unpack ml packed object 
      ml_tlm2_unpack_create(v, t1);

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)t1;
      tx->acquire();

      // Update transaction fields
      trans.set_address(tx->get_address());
      trans.set_response_status(tx->get_response_status());
      if(trans.is_read()) {
	ml_tlm2_update_data_from_response(trans, *tx, m_socket_name);
      }
      trans.update_extensions_from(*tx);

      uvm_ml_utils::release_mlupo_to_pool(v);
      tx->release();

      return ret;
    }

    unsigned int transport_dbg(uvm_ml_packed_obj& vt, sc_time_unit time_unit, double time_value) {
      tlm_generic_payload * tlm_gp = 0;

      ml_tlm2_unpack_create(&vt, tlm_gp);

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)tlm_gp;

      //assert(tx->has_mm());
      if(!(tx->has_mm())) {
	UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: transport_dbg failed because the transaction has no memory manager","");
	return 0;
      };
      tx->acquire();

      // send a TLM2 transaction to the DUT
      unsigned ret = isocket->transport_dbg(*(dynamic_cast<REQ *>(tx)));

      // Pack into ml packed object
      ml_tlm2_pack(*tlm_gp, &vt);

      tx->release();
      return ret;
    }

    void invalidate_direct_mem_ptr(sc_dt::uint64 start_range, sc_dt::uint64 end_range){};    

private:
  
    inline void set_transaction_mapping() {
      if (!disable_transaction_mapping_set) {
	disable_transaction_mapping = ml_tlm2_transaction_mapping_disabled(m_socket_name);
	disable_transaction_mapping_set = true;
      };
    }
  }; // class ml_tlm2_target_connector



// Initiator connector 
// adapter for propagating transactions from SC initiator to testbench
/*! \class ml_tlm2_initiator_connector
  \brief Template of TLM2 initiator connector.

  Templated by type of the transaction, the bus width and protocol types
  Implements the methods and tasks needed for ML TLM2 communication 
*/
template <class REQ, unsigned int BUSWIDTH, typename TYPES = tlm::tlm_base_protocol_types>
class ml_tlm2_initiator_connector: public ml_tlm2_initiator_connector_base
  ,virtual public tlm::tlm_fw_transport_if<TYPES>
  {
    public :
    typedef typename TYPES::tlm_payload_type transaction_type;
    tlm::tlm_target_socket<BUSWIDTH, TYPES> tsocket;

    // transaction mapping for nb calls
    bool disable_transaction_mapping;
    bool disable_transaction_mapping_set;
    std::string m_socket_name;
    
    // constructor
    ml_tlm2_initiator_connector(sc_module_name name_, tlm_initiator_socket<BUSWIDTH,TYPES> &s, std::string sname) :
    tsocket("tsocket"),
    disable_transaction_mapping(false),
    disable_transaction_mapping_set(false),
    m_socket_name(sname)
    {
      tsocket(*this);
      s.bind(tsocket);
      register_top_of_the_socket_name(sname);
      ml_tlm2_do_register_initiator(sname,name());
      is_target = false; 
      
      //add to socket map
      uvm_ml_utils::add_socket(sname, this);
    }
    
    void b_transport(REQ& trans, sc_time& delay) {
      sc_time_unit time_unit;
      double       time_value;
      sc_time_unit delay_unit;
      double       delay_value;
      tlm_generic_payload * t1 = 0;

      if (trans.get_data_ptr() == NULL) {
	SC_REPORT_FATAL("Error", "ml_tlm2_connector: transaction has NULL data pointer");
	trans.set_response_status(TLM_GENERIC_ERROR_RESPONSE);
	return;
      };

      // Pack transaction into ml packed object
      uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
      uvm_ml_utils::allocate_mlupo(v);

      ml_tlm2_pack(trans, v);

      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(delay);
      delay_value = delay_struct.delay_value;
      delay_unit = (sc_time_unit)delay_struct.tu;

      sc_time ct = sc_time_stamp();
      delay_struct = global_tp->get_delay_struct(ct);
      time_value= delay_struct.delay_value;
      time_unit = (sc_time_unit)delay_struct.tu;

      // Call testbench
      uvm_ml_tlm_trans::tlm2_b_transport(conn_id, v, &delay_unit, &delay_value);

      delay = sc_time(delay_value, (sc_time_unit)(delay_unit));
     
      // Unpack ml packed object
      ml_tlm2_unpack_create(v, t1);

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)t1;
      //assert(tx != NULL);
      if(tx == NULL) {
	UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: b_transport failed because the transaction is NULL","");
	return;
      };
      tx->acquire();

      // update transaction fields
      trans.set_address(tx->get_address());
      trans.set_response_status(tx->get_response_status());
      if(trans.is_read())
	ml_tlm2_update_data_from_response(trans, *(tx), m_socket_name);
      trans.update_extensions_from(*t1);

      uvm_ml_utils::release_mlupo_to_pool(v);

      tx->release();
    }

    tlm_sync_enum nb_transport_fw(REQ& trans, tlm_phase& phase, sc_time& delay) {
      sc_time_unit time_unit;
      double       time_value;
      sc_time_unit delay_unit;
      double       delay_value;
      unsigned int transaction_id = ML_TLM2_UNINITIALIZED_ID;
      tlm_generic_payload * t1 = 0;

      // map transaction if needed
      set_transaction_mapping();      
      if (disable_transaction_mapping == false) {
	// make sure transaction has a memory manager      
	if (!trans.has_mm()) {
	  ml_tlm2_transaction_mapping_mm_error(m_socket_name);
	}
	if (phase == BEGIN_REQ) {	
	  ml_tlm2_map_transaction(&trans, transaction_id);      
	} else if (phase == END_RESP /*|| status == TLM_COMPLETED*/) {
	  transaction_id = ml_tlm2_get_id_by_transaction(trans);
	  if (transaction_id == ML_TLM2_UNINITIALIZED_ID) {
	    ml_tlm2_transaction_mapping_update_error(m_socket_name,"nb_transport_fw",phase);
	  }
	}
      }

      // Pack to ml packed object
      uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
      uvm_ml_utils::allocate_mlupo(v);

      ml_tlm2_pack(trans, v);

      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(delay);
      delay_value = delay_struct.delay_value;
      delay_unit = (sc_time_unit)delay_struct.tu;
      tlm_phase_enum phase_id = (tlm_phase_enum)(unsigned int)phase;

      sc_time ct = sc_time_stamp();
      delay_struct = global_tp->get_delay_struct(ct);
      time_value= delay_struct.delay_value;
      time_unit = (sc_time_unit)delay_struct.tu;

      // Call testbench
      tlm_sync_enum ret = (tlm_sync_enum) uvm_ml_tlm_trans::tlm2_nb_transport_fw(conn_id, 
											     v, 
											     (unsigned int *)&phase_id,
                                                                                             transaction_id,
											     &delay_unit, 
											     &delay_value
											     );

      phase = phase_id;
      delay = sc_time(delay_value, (sc_time_unit)(delay_unit));

      // Unpack ml packed object 
      ml_tlm2_unpack_create(v, t1);

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)t1;
      tx->acquire();

      // Update transaction fields
      trans.set_address(tx->get_address());
      trans.set_response_status(tx->get_response_status());
      if(trans.is_read())
	ml_tlm2_update_data_from_response(trans, *tx, m_socket_name);
      trans.update_extensions_from(*tx);

      // release transaction from map if needed
      if ((disable_transaction_mapping == false) && (phase == END_RESP || ret == TLM_COMPLETED)) {
	bool result = ml_tlm2_release_transaction(t1, transaction_id);
	if (!result) { // may have been removed already by target connector
	  //ml_tlm2_transaction_mapping_remove_error(m_socket_name,"nb_transport_fw",phase,ret);
	}
      }

      uvm_ml_utils::release_mlupo_to_pool(v);

      tx->release();
      return ret;
    }

    tlm_sync_enum nb_transport_bw(uvm_ml_packed_obj& vt, tlm_phase_enum *phase, unsigned int transaction_id, sc_time_unit *delay_unit, double *delay_value, sc_time_unit time_unit, double time_value) {
      tlm_generic_payload * tlm_gp = 0;
      transaction_type * actual_trans;

      ml_tlm2_unpack_create(&vt, tlm_gp);
      //assert(tlm_gp->has_mm());    
      if(!(tlm_gp->has_mm())) {
	UVM_ML_SC_REPORT_ERROR("UVM-SC adapter: nb_transport_bw failed because the transaction had no memory manager","");
	return TLM_COMPLETED;
      };

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)tlm_gp;

      sc_time delay = sc_time(*delay_value, (sc_time_unit)*delay_unit);
      tlm_phase bw_phase(*phase);

      // if transaction is mapped, fetch original object
      if ((disable_transaction_mapping == false) && 
          (*phase == END_REQ || *phase == BEGIN_RESP)) {
	// retrieve the original gp sent on the forward path
	transaction_type *mapped_trans = 
	  dynamic_cast<transaction_type*>(ml_tlm2_get_transaction_by_id(transaction_id));
	if (!mapped_trans) {
	  ml_tlm2_transaction_mapping_update_error(m_socket_name,"nb_transport_bw",*phase);
	}
	
	// update original transaction with tx transaction fields
	ml_tlm2_bw_update_gp(*mapped_trans, *tx);
	// in case of a read transaction, need to copy the data as well
	if (mapped_trans->is_read()) {
	  ml_tlm2_update_data_from_response(*mapped_trans, *(tx), m_socket_name);
	}
	actual_trans = mapped_trans;                  
	// need to acquire then release the temp transaction to make sure memory is cleared
	tx->acquire();
	tx->release();
      } else {
	actual_trans = tx;
      };

      actual_trans->acquire();

      // send a TLM2 transaction to the DUT
      tlm_sync_enum ret = tsocket->nb_transport_bw(*(dynamic_cast<REQ *>(actual_trans)), bw_phase, delay);

      *phase = (tlm_phase_enum)(unsigned int) bw_phase;

      // Reconstruct delay
      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(delay);
      *delay_value= delay_struct.delay_value;
      *delay_unit = (sc_time_unit)delay_struct.tu;

      // Pack into ml packed object
      ml_tlm2_pack(*actual_trans, &vt);

      // release transaction from map if needed
      if ((disable_transaction_mapping == false) && 
          (bw_phase == END_RESP || ret == TLM_COMPLETED)) {      
	bool result = ml_tlm2_release_transaction(actual_trans, transaction_id);
	if (!result) {
	  ml_tlm2_transaction_mapping_remove_error(m_socket_name,"nb_transport_bw",bw_phase,ret);
	}      
      }

      actual_trans->release();
      return ret;
    }

    unsigned int transport_dbg(REQ& trans) {
      sc_time_unit time_unit;
      double       time_value;
      tlm_generic_payload *t1 = 0;

      // Pack to ml packed object
      uvm_ml_packed_obj* v = uvm_ml_utils::get_mlupo_from_pool();
      uvm_ml_utils::allocate_mlupo(v);

      ml_tlm2_pack(trans, v);

      sc_time ct = sc_time_stamp();
      ml_tlm2_delay_val delay_struct = global_tp->get_delay_struct(ct);
      time_value= delay_struct.delay_value;
      time_unit = (sc_time_unit)delay_struct.tu;

      // Call testbench
      unsigned ret = uvm_ml_tlm_trans::tlm2_transport_dbg(conn_id, v);

      // Unpack ml packed object
      ml_tlm2_unpack_create(v, t1);

      // Extract tlm_gp
      transaction_type * tx = (transaction_type *)t1;
      tx->acquire();

      // Update transaction fields
      trans.set_address(tx->get_address());
      trans.set_response_status(tx->get_response_status());
      if(trans.is_read())
	ml_tlm2_update_data_from_response(trans, *tx, m_socket_name);
      trans.update_extensions_from(*tx);

      uvm_ml_utils::release_mlupo_to_pool(v);

      tx->release();
      return ret;
    }
    
    virtual bool get_direct_mem_ptr(REQ& trans, tlm::tlm_dmi& dmi_data) {
      return false; 
    }

private:
  
    inline void set_transaction_mapping() {
      if (!disable_transaction_mapping_set) {
	disable_transaction_mapping = ml_tlm2_transaction_mapping_disabled(m_socket_name);
	disable_transaction_mapping_set = true;
      };
    }
  }; // class ml_tlm2_initiator_connector

#endif // _ML_TLM2_CONNECTOR_H_
