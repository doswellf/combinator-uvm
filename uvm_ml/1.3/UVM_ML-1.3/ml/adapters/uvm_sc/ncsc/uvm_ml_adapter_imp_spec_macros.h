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
/*! \file ncsc/uvm_ml_adapter_imp_spec_macros.h
  \brief OS specific variant of macro definitions.
*/
#ifndef UVM_ML_ADAPTER_IMP_SPEC_MACROS_H
#define UVM_ML_ADAPTER_IMP_SPEC_MACROS_H

// FIXME - move all this stuff into a separate header provided by the framework

extern "C" void uvm_ml_ncsc_set_fli_import_call (bool arg);

extern "C" void uvm_ml_ncsc_start_systemc_context();
extern "C" void uvm_ml_ncsc_stop_systemc_context();




#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_1 \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);	\
  uvm_ml_ncsc_print_sc_report_message(x);		  \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const ::std::exception& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);			\
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const char* s ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);	\
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( ... ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);		     \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
}

#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_INT \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);	\
  uvm_ml_ncsc_print_sc_report_message(x);		  \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const ::std::exception& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);			\
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( const char* s ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);	\
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
} \
catch( ... ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);		     \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return 0; \
}

#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_2_VOID \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);	\
  uvm_ml_ncsc_print_sc_report_message(x);		  \
  report_tlm1_error(rec); \
  return; \
} \
catch( const ::std::exception& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);			\
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( const char* s ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);	\
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
} \
catch( ... ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false);		     \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(rec); \
  return; \
}

#define CATCH_KERNEL_EXCEPTION_IN_RECEIVER_3 \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_print_sc_report_message(x);		\
  report_tlm1_error(rec); \
  return; \
} \
catch( const ::std::exception& x ) \
{ \
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
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
  uvm_ml_ncsc_set_fli_import_call(false); \
  uvm_ml_ncsc_print_sc_report_message(x); \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
} \
catch( const ::std::exception& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
} \
catch( const char* s ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << s << ::std::endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
} \
catch( ... ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_connector_error(conn); \
  return UVM_ML_TLM2_COMPLETED; \
}

#define CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_2 \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  uvm_ml_ncsc_print_sc_report_message(x); \
  report_tlm1_error(conn); \
  return 0; \
} \
catch( const ::std::exception& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
  report_tlm1_error(conn); \
  return 0; \
} \
catch( const char* s ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << s << ::std::endl; \
  report_tlm1_error(conn); \
  return 0; \
} \
catch( ... ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_tlm1_error(conn); \
  return 0; \
}

#define CATCH_KERNEL_EXCEPTION_IN_CONNECTOR_3 \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_print_sc_report_message(x); \
  report_connector_error(conn); \
  return; \
} \
catch( const ::std::exception& x ) \
{ \
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
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
  uvm_ml_ncsc_set_fli_import_call(false); \
  uvm_ml_ncsc_print_sc_report_message(x); \
  report_connector_error(conn); \
  return 1; \
} \
catch( const ::std::exception& x ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
  report_connector_error(conn); \
  return 1; \
} \
catch( const char* s ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << s << ::std::endl; \
  report_connector_error(conn); \
  return 1; \
} \
catch( ... ) \
{ \
  uvm_ml_ncsc_set_fli_import_call(false); \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  report_connector_error(conn); \
  return 1; \
}


namespace sc_core {
enum uvm_ml_kernel_exception_message
{
  UVM_ML_QUASI_STATIC_ELABORATION,
  UVM_ML_CREATE_SC_INST,
  UVM_ML_CREATE_SC_INST_2
};

extern "C" void uvm_ml_ncsc_handle_sc_kernel_exception_message
(
 enum uvm_ml_kernel_exception_message kernel_exception_message,
 const char* string1,
 const char* string2
);
// return "m"

#define UVM_ML_CATCH_SC_KERNEL_EXCEPTION_1(n, m, s1, s2)        \
catch( const sc_report& x ) \
{ \
  uvm_ml_ncsc_print_sc_report_message(x); \
  uvm_ml_ncsc_handle_sc_kernel_exception_message(n,s1, s2);     \
  return m; \
} \
catch( const ::std::exception& x ) \
{ \
  ::std::cout << "\n" << ncsc_report_compose_message(x) << ::std::endl; \
    uvm_ml_ncsc_handle_sc_kernel_exception_message(n, s1, s2);           \
  return m; \
} \
catch( const char* s ) \
{ \
  ::std::cout << "\n" << s << ::std::endl; \
  uvm_ml_ncsc_handle_sc_kernel_exception_message(n, s1, s2); \
  return m; \
} \
catch( ... ) \
{ \
  ::std::cout << "\n" << "UNKNOWN EXCEPTION OCCURED" << ::std::endl; \
  uvm_ml_ncsc_handle_sc_kernel_exception_message(n, s1, s2); \
  return m; \
}
// no "return"

}


#define CURRENT_SIMCONTEXT() sc_get_curr_simcontext()


#define INVISIBLE_EVENT(name) sc_event(name, false)


extern "C" sc_core::sc_module* uvm_ml_ncsc_quasi_static_construct_top(const std::string& name1, const std::string& name2);

#define QUASI_STATIC_CONSTRUCT_TOP(name1,name2) uvm_ml_ncsc_quasi_static_construct_top((name1),(name2))


#define INITIALIZE_FRAMEWORK_IF_NEEDED() -1

// Co-simulation stubs


#define ENTER_CO_SIMULATION_CONTEXT() uvm_ml_ncsc_set_fli_import_call(true)

#define ENTER_CO_SIMULATION_CONTEXT2() uvm_ml_ncsc_set_fli_import_call(true)

#define ENTER_CO_SIMULATION_CONTEXT3() {  ENTER_CO_SIMULATION_CONTEXT(); uvm_ml_ncsc_start_systemc_context(); } 


#define EXIT_CO_SIMULATION_CONTEXT() uvm_ml_ncsc_set_fli_import_call(false)

#define EXIT_CO_SIMULATION_CONTEXT2() uvm_ml_ncsc_set_fli_import_call(false)

#define EXIT_CO_SIMULATION_CONTEXT3()

#define EXIT_CO_SIMULATION_CONTEXT4() { EXIT_CO_SIMULATION_CONTEXT3(); uvm_ml_ncsc_stop_systemc_context(); }

#define EXIT_CO_SIMULATION_CONTEXT5() { EXIT_CO_SIMULATION_CONTEXT();  } 

#define CO_SIMULATION_EXECUTE_DELTA() 0;

namespace uvm_ml { 
    bool in_elaboration();
}

#define IN_ELABORATION() uvm_ml::in_elaboration()


#define EXCEPTION_HANDLER_STORAGE() void* icc_root = 0
#define STORE_OLD_EXCEPTION_HANDLER() icc_root = ncsc_push_dpi_icc_exception_catcher()
#define RESTORE_OLD_EXCEPTION_HANDLER()       ncsc_pop_dpi_icc_exception_catcher(icc_root)

#define SC_KILL_CATCHER()   catch( const sc_kill_exception& x)  \
  { \
    ncsc_pop_dpi_icc_exception_catcher(icc_root); \
    uvm_ml_ncsc_set_fli_import_call(false); \
    if (icc_root) { \
      return 1; \
    } \
    return ret; \
  }

#define UVM_ML_REPORT_COMPOSE_MESSAGE(x) cout << "\n" << ncsc_report_compose_message(x) << "\n"

#ifdef NCSC_DEBUG
#define ASSERT_N_WORDS(words, number) assert(words < (number))
#else
#define ASSERT_N_WORDS(words, number)
#endif

#ifdef NCSC_DEBUG
#define ASSERT_ZERO(var) assert(var == 0)
#else
#define ASSERT_ZERO(var)
#endif

#define UVM_ML_SC_REPORT_ERROR(msg1, msg2) SC_REPORT_ERROR(msg1, msg2)

#define UVM_ML_SC_PRINT_REPORT(ex) uvm_ml_ncsc_print_sc_report_message((ex))

#define CURRENT_SIMCONTEXT_SET_ERROR() CURRENT_SIMCONTEXT()->set_error()


#define EXTERN_DISABLE_SC_START
#define DISABLE_SC_START()

#endif
