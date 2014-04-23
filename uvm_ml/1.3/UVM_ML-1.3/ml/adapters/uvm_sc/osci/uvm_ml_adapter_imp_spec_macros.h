//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
//   Copyright 2013 Advanced Micro Devices Inc.
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

/*! \file osci/uvm_ml_adapter_imp_spec_macros.h
  \brief OS specific variant of macro definitions.
*/
#ifndef UVM_ML_ADAPTER_IMP_SPEC_MACROS_H
#define UVM_ML_ADAPTER_IMP_SPEC_MACROS_H

#include "uvm_ml_adapter_imp_spec_headers.h"

#define UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(n, m, s1, s2) \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl;	 \
  handle_sc_kernel_exception_message(n, s1, s2); \
  return m; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl;	 \
  handle_sc_kernel_exception_message(n, s1, s2); \
  return m; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  handle_sc_kernel_exception_message(n, s1, s2); \
  return m; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  handle_sc_kernel_exception_message(n, s1, s2); \
  return m; \
}


#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1 \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
}


#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_VOID \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
}

#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_INT \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return 0 ; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
}

#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_3 \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
}

#define CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_1 \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
}


#define CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_3 \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_connector_error(conn); \
  return; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_connector_error(conn); \
  return; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_connector_error(conn); \
  return; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_connector_error(conn); \
  return; \
}

#define CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_4 \
catch( const sc_report& x ) \
{ \
  cout << x.what() << endl; \
  report_connector_error(conn); \
  return 1; \
} \
catch( const ::std::exception& x ) \
{ \
  cout << x.what() << endl; \
  report_connector_error(conn); \
  return 1; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  report_connector_error(conn); \
  return 1; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_connector_error(conn); \
  return 1; \
}



// Error messages

#define ML_UVM_RUN_TIME_ERROR_ "Error ocurred in processing an ML-UVM function call in SystemC"

#define ML_UVM_MISSING_REGISTRATION_ "No UVM_COMPONENT_REGISTER macro or NCSC_MODULE_EXPORT macro found for SystemC object"

#define ML_UVM_OBJ_NOT_FOUND_ "Port/export specifed in mixed-language UVM connection function not found"

#define ML_UVM_NO_TRANS_REC_ "Port/export specifed in mixed-language UVM connection function has not been registered using uvm_ml_register()"

#define UVM_CONNECTOR_ID_NOT_FOUND_ "uvm connector id not found"

#define ML_UVM_NO_MULTIPORT_ "Port registered using uvm_ml_register() is being connected more than once"

#define UVM_RECEIVER_NOT_VALID_ "uvm receiver not valid"

#define UVM_TRANSMITTER_NOT_VALID_ "uvm transmitter not valid"

#define ML_UVM_UNCONNECTED_ID_ "Port/export is being accessed that has been registered using uvm_ml_register(), but has not been connected using a mixed-language UVM connection function"

#define ML_UVM_UNIMPLEMENTED_INTERFACE_ "The interface is not implemented"

#define UVM_TRANSMITTER_FUNC_NOT_IMPL_ "uvm function not implemented by transmitter"
#define UVM_RECEIVER_FUNC_NOT_IMPL_ "uvm function not implemented by receiver"

#define ML_UVM_UNKNOWN_CALL_ID_ "Unknown call ID"

#define ML_UVM_SIZE_LIMIT_ "Size of SystemC uvm_object exceeds the maximum size that can be passed across UVM-ML boundary"

#define UVM_PORT_IFACE_ "uvm port interface does not implement function"


// Quasi-static


#define QUASI_STATIC_CONSTRUCT_TOP(name1,name2) quasi_static_construct_top(name1,name2)


#define UVM_ML_QUASI_STATIC_END_OF_CONSTRUCTION() sc_get_curr_simcontext()->quasi_static_end_of_construction()

#define UVM_ML_QUASI_STATIC_CONNECT() sc_get_curr_simcontext()->quasi_static_connect()

#define UVM_ML_QUASI_STATIC_END_OF_ELABORATION() sc_get_curr_simcontext()->quasi_static_end_of_elaboration()

#define UVM_ML_QUASI_STATIC_START_OF_SIMULATION() sc_get_curr_simcontext()->quasi_static_start_of_simulation()


// Misc

#define CURRENT_SIMCONTEXT() sc_get_curr_simcontext()

#define CO_SIMULATION_EXECUTE_DELTA() (CURRENT_SIMCONTEXT()->co_simulate(SC_ZERO_TIME), 1)

#define ENTER_CO_SIMULATION_CONTEXT() \
    if (((unsigned) time_unit) <= ((unsigned) (sc_time_unit) SC_SEC)) { \
        sc_time duration = sc_time(time_value, (sc_time_unit)time_unit); \
        CURRENT_SIMCONTEXT()->co_simulate(duration - sc_time_stamp());	\
    } \
    else \
        CURRENT_SIMCONTEXT()->co_simulate(SC_ZERO_TIME);

#define ENTER_CO_SIMULATION_CONTEXT2() 


#define ENTER_CO_SIMULATION_CONTEXT3() ENTER_CO_SIMULATION_CONTEXT();



#define EXIT_CO_SIMULATION_CONTEXT()

#define EXIT_CO_SIMULATION_CONTEXT2() CURRENT_SIMCONTEXT()->co_simulate(SC_ZERO_TIME)

#define EXIT_CO_SIMULATION_CONTEXT3() CURRENT_SIMCONTEXT()->co_simulate(SC_ZERO_TIME)

#define EXIT_CO_SIMULATION_CONTEXT4() EXIT_CO_SIMULATION_CONTEXT3();
#define EXIT_CO_SIMULATION_CONTEXT5() EXIT_CO_SIMULATION_CONTEXT();

#define IN_ELABORATION() (false)


#define INVISIBLE_EVENT(name) sc_event()

#define EXCEPTION_HANDLER_STORAGE()

#define STORE_OLD_EXCEPTION_HANDLER()

#define RESTORE_OLD_EXCEPTION_HANDLER()

#define SC_KILL_CATCHER()

#define UVM_ML_REPORT_COMPOSE_MESSAGE(x) cout << x.what() << endl

#define INITIALIZE_FRAMEWORK_IF_NEEDED() uvm_ml_utils::initialize_adapter()


#define ASSERT_N_WORDS(words, number)


#define ASSERT_ZERO(var)

#define UVM_ML_SC_REPORT_ERROR(msg1, msg2) SC_REPORT_ERROR(msg1,"\n")

#define UVM_ML_SC_PRINT_REPORT(ex) cout << (ex).what() << endl


#if (SYSTEMC_VERSION >= 20120701) // OSCI 2.3
#define CURRENT_SIMCONTEXT_SET_ERROR() CURRENT_SIMCONTEXT()->set_error(sc_handle_exception()) 
#else
#define CURRENT_SIMCONTEXT_SET_ERROR() CURRENT_SIMCONTEXT()->set_error() 
#endif
#define DISABLE_SC_START() uvm_ml_sc_changes::disable_sc_start()

#define EXTERN_DISABLE_SC_START \
    namespace uvm_ml_sc_changes { \
    extern void disable_sc_start(); \
    }



#endif
