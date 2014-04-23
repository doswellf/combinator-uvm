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

#include "sn_uvm_ml_adapter.h"
#include <dlfcn.h>

#define UVM_ML_ADAPTER (GLOB_SIM->ml_lib_adapter)
#define CREATE_UVM_ML_ADAPTER_IF_NEEDED SN_DISPATCH(create_ml_lib_adapter,GLOB_SIM,simulator,(GLOB_SIM))

#define ADAPTER_DBG_NAME "UVM_ML e-ADAPTER >>"
#define DEBUG_MSG(direction,func,...)				\
  if (debug) {							\
    printf("%s %s %s() ",ADAPTER_DBG_NAME,direction,func);	\
    printf(__VA_ARGS__);					\
    printf("\n");						\
  }
#define ENTER_DEBUG_MSG(func,...)				\
  DEBUG_MSG("Entering",func,__VA_ARGS__)			
#define EXIT_DEBUG_MSG(func,...)				\
  DEBUG_MSG("Exiting",func,__VA_ARGS__)			
#define ENTER_DEBUG_MSG_VOID(func)		\
  ENTER_DEBUG_MSG(func,"")
#define EXIT_DEBUG_MSG_VOID(func)		\
  EXIT_DEBUG_MSG(func,"")

static int sn_uvm_ml_adapter_id = -1; 
static bp_api_struct * provided_tray = NULL; /* holds Backplane functions tray */
static bp_frmw_c_api_struct required_tray = {0}; /* holds Specman functions tray */
static SN_TYPE(bool) sys_added = FALSE;
static int debug = 0;
static node * e_tops; /* top of a linked list for all e loaded modules */

static void fill_bp_required_tray();
static void add_node(char *);
static char * pop0_node_data();

/* Backplane registration function - this function is called during 
   boot time or explicitly from Specman prompt */
SN_TYPE(bool) sn_register_uvm_ml_adapter() {
  typedef bp_api_struct * (*bp_get_provided_tray_ptr_type) (void);
  bp_get_provided_tray_ptr_type bp_get_provided_tray_ptr = 0;
  char *bp_version;
  SN_TYPE(bool) result = TRUE;

  char * sn_indicators[2];
  
  ENTER_DEBUG_MSG_VOID("sn_register_uvm_ml_adapter");

  /* Specman was not registered already */
  if (sn_uvm_ml_adapter_id == -1) {

    sn_indicators[0] = "e";
    sn_indicators[1] = "";

    bp_get_provided_tray_ptr = dlsym(NULL,"bp_get_provided_tray");
    
    debug = getenv("UNILANG_DEBUG_MODE") || getenv("UVM_ML_DEBUG_MODE");
    
    if ( debug ) {
      printf("%s sn_register_uvm_ml_adapter(): bp_get_provided_tray_ptr = %p\n",ADAPTER_DBG_NAME,bp_get_provided_tray_ptr);   
    }
    
    if (bp_get_provided_tray_ptr) {
      provided_tray = (*bp_get_provided_tray_ptr)();
    }

    bp_version =  provided_tray->get_version_ptr(); 
       
    if ( debug ) {
      printf("%s sn_register_uvm_ml_adapter(): Backplane version = %s Specman backplane version = %s\n",ADAPTER_DBG_NAME,bp_version,SN_UVM_ML_VERSION);
    }
    
    if (strcmp(bp_version,SN_UVM_ML_VERSION)) {
      fprintf(stderr,"\n *** Error: Version of the UVM-ML Specman adapter does not match UVM-ML version\n");  
      result = FALSE;
    }
    
    if (result) {
      fill_bp_required_tray();
      
      sn_uvm_ml_adapter_id = provided_tray->register_framework_ptr("Specman",sn_indicators,&required_tray);
      
      if ( debug ) {
	printf("%s sn_register_uvm_ml_adapter(): sn_uvm_ml_adapter_id = %d\n",ADAPTER_DBG_NAME,sn_uvm_ml_adapter_id);
      }
    }
  }

  EXIT_DEBUG_MSG("sn_register_uvm_ml_adapter","result = %d",result);
  
  return result;
  
}

/*                            */
/* Backplane to Specman calls */
/*                            */

/* Backplane shall call this function for each e module name given 
   in -uvmtop/-uvmtest. For the first one we return sys to be 
   Specman most top hierarchy. For the rest we return NULL since 
   there is only one valid sys */
static char * sn_bp_get_top_component_for_arg(char * arg)
{
  char * result;

  ENTER_DEBUG_MSG("sn_bp_get_top_component_for_arg","arg = %s",arg);
  
  if (sys_added) {
    result = NULL;
  } else {
    sys_added = TRUE;
    result = "sys";
  }

  /* We bufferize the top e files and load them later in sn_bp_add_top() */
  add_node(strdup(arg));

  EXIT_DEBUG_MSG("sn_bp_get_top_component_for_arg","result = %s",result);

  return result;
}

static int sn_bp_startup() 
{
  int result = 1; /* 1 - success, 0 - error */
  char err_msg [1000];
  char * e_top = NULL;
  char * sn_load_cmd = NULL;
  int e_top_len, cmd_res;

  ENTER_DEBUG_MSG_VOID("sn_bp_startup");
  
  if (!sys_added) {
    provided_tray->add_root_node_ptr(sn_uvm_ml_adapter_id,0,"sys","sys");
    sys_added = TRUE;
  }
  
  CREATE_UVM_ML_ADAPTER_IF_NEEDED;
  
  while (result && (e_top = pop0_node_data())) {
    
    if ( debug) {
      printf("%s sn_bp_startup(): e_top = %s\n",ADAPTER_DBG_NAME,e_top);
    }

    e_top_len = strlen(e_top);   
 
    /* arg is not ended with ".e"  is not supported */
    if (e_top[e_top_len-1] != 'e' || e_top[e_top_len-2] != '.') {
      sprintf(err_msg,"*** Error: \"%s\" was given to -uvmtop/uvm_ml_run_test() as argument. Only e file is a valid argument.",e_top);
      SN_DISPATCH(sn_ml_out,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,err_msg));
      result = 0;
    } else {
      sn_load_cmd = malloc(e_top_len+15);
    
      strcpy(sn_load_cmd,"load -if ");
      strcat(sn_load_cmd,e_top);

      if ( debug ) {
	printf("%s sn_bp_startup(): Specman command = %s\n",ADAPTER_DBG_NAME,sn_load_cmd);
      }

      cmd_res = sn_esi_do_commands(0,sn_load_cmd);
      
      free(sn_load_cmd);
      free(e_top);
   
      if (cmd_res) { /* we had an error during load */
	result = 0;
      }
    } 
  }

  if (result) { 
    /* After we loaded all the files we can call setup() */
    SN_DISPATCH(sn_ml_init_phases,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER));
  } else { /* error case, let's clean the list */
    while (e_top = pop0_node_data()) {
      free(e_top);
    }
  }
  
  EXIT_DEBUG_MSG("sn_bp_startup","result = %d",result);
  return result;  
}

static int sn_bp_add_top(const char *top_identifier, 
			 const char *instance_name)
{
  char err_msg [1000];
  int result = 0; /* sys instance id */

  ENTER_DEBUG_MSG("sn_bp_add_top","top_identifier = %s",top_identifier);

  /* There is an instance name and it's not sys */
  if (instance_name && strcmp(instance_name,"sys")) {
    sprintf(err_msg,"*** Error: You can't use an instance name for Specman. \"%s\" instance name was given.",instance_name);
    SN_DISPATCH(sn_ml_out,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,err_msg)); 
    result = -1;
  } 

  EXIT_DEBUG_MSG("sn_bp_add_top","result = %d",result);

  return result;
}

/* This is the first method to be called by backplane in debug mode */
static void sn_bp_set_debug_mode(int mode)    
{
  ENTER_DEBUG_MSG("sn_bp_set_debug_mode","mode = %d",mode);

  debug = 1;

  if (GLOB && GLOB_SIM) {
    CREATE_UVM_ML_ADAPTER_IF_NEEDED;
    SN_DISPATCH(sn_ml_set_debug_mode,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,mode));
  }    
  
  EXIT_DEBUG_MSG_VOID("sn_bp_set_debug_mode");
}

static int sn_bp_find_connector_id_by_name (const char * path)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_find_connector_id_by_name","path = %s",path);
  result = SN_DISPATCH(sn_ml_find_connector_id_by_name,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,path));
  EXIT_DEBUG_MSG("sn_bp_find_connector_id_by_name","result = %d",result);
  return result;
}

static int sn_bp_get_connector_type(unsigned connector_id)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_get_connector_type","connector_id = %d",connector_id);
  result = SN_DISPATCH(sn_ml_get_connector_type,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id));
  EXIT_DEBUG_MSG("sn_bp_get_connector_type","result = %d",result);
  return result;
}

static unsigned sn_bp_is_export_connector(unsigned connector_id)
{
  unsigned result;
  ENTER_DEBUG_MSG("sn_bp_is_export_connector","connector_id = %d",connector_id);
  result = SN_DISPATCH(sn_ml_is_export_connector,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id));
  EXIT_DEBUG_MSG("sn_bp_is_export_connector","result = %d",result);
  return result;
}

static const char * sn_bp_get_connector_intf_name(unsigned connector_id)
{
  char * result;
  ENTER_DEBUG_MSG("sn_bp_get_connector_intf_name","connector_id = %d",connector_id);
  result = (char *)SN_DISPATCH(sn_ml_get_connector_intf_name,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id));
  EXIT_DEBUG_MSG("sn_bp_get_connector_intf_name","result = %d",result);
  return result;
}

static char* sn_bp_get_connector_T1_name(int port_id)
{
  char* result;
  ENTER_DEBUG_MSG("sn_bp_get_connector_T1_name","port_id = %d",port_id);
  result = (char *)SN_DISPATCH(sn_ml_get_connector_T1_name,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,port_id));
  EXIT_DEBUG_MSG("sn_bp_get_connector_T1_name","result = %d",result);
  return result;
}

static char* sn_bp_get_connector_T2_name(int port_id)
{
  char* result;
  ENTER_DEBUG_MSG("sn_bp_get_connector_T2_name","port_id = %d",port_id);
  result = (char *)SN_DISPATCH(sn_ml_get_connector_T2_name,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,port_id));
  EXIT_DEBUG_MSG("sn_bp_get_connector_T2_name","result = %d",result);
  return result;
}

/* TLM1 calls */
static int sn_bp_try_put_bitstream(unsigned connector_id, 
				   unsigned stream_size,
				   uvm_ml_stream_t stream,
				   uvm_ml_time_unit time_unit,
				   double time_value)
{
  unsigned result;
  ENTER_DEBUG_MSG("sn_bp_try_put_bitstream","connector_id = %d, stream_size = %d, stream = %p, time_unit = %d, time_value = %f",
		  connector_id,stream_size,stream,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_try_put_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,stream_size,stream));
  EXIT_DEBUG_MSG("sn_bp_try_put_bitstream","result = %d",result);
  return result;
}

static int sn_bp_can_put(unsigned connector_id, 
			 uvm_ml_time_unit time_unit, 
			 double time_value)
{
  unsigned result;
  ENTER_DEBUG_MSG("sn_bp_can_put","connector_id = %d, time_unit = %d, time_value = %f",connector_id,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_can_put,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id));
  EXIT_DEBUG_MSG("sn_bp_can_put","result = %d",result);
  return result;
}

static int sn_bp_try_get_bitstream(unsigned connector_id, 
				   unsigned int * stream_size_ptr, 
				   uvm_ml_stream_t stream,
				   uvm_ml_time_unit time_unit, 
				   double time_value)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_try_get_bitstream","connector_id = %d, stream_size_ptr = %p, stream = %p, time_unit = %d, time_value = %f",
		  connector_id,stream_size_ptr,stream,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_try_get_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,stream_size_ptr,stream));
  EXIT_DEBUG_MSG("sn_bp_try_get_bitstream","stream_size_ptr = %d, result = %d",*stream_size_ptr, result);
  return result;
}

static int sn_bp_can_get(unsigned connector_id,
			 uvm_ml_time_unit time_unit,
			 double time_value)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_can_get","connector_id = %d, time_unit = %d, time_value = %f",connector_id,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_can_get,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id));
  EXIT_DEBUG_MSG("sn_bp_can_get","result = %d",result);
  return result;
}

static int sn_bp_try_peek_bitstream(unsigned connector_id,
				    unsigned * stream_size_ptr,
				    uvm_ml_stream_t stream,
				    uvm_ml_time_unit time_unit,
				    double time_value)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_try_peek_bitstream","connector_id = %d, stream_size_ptr = %p, stream = %p, time_unit = %d, time_value = %f",
		  connector_id,stream_size_ptr,stream,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_try_peek_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,stream_size_ptr,stream));
   EXIT_DEBUG_MSG("sn_bp_try_peek_bitstream","stream_size_ptr = %d, result = %d",*stream_size_ptr, result);
  return result;
}

static int sn_bp_can_peek(unsigned connector_id,
			  uvm_ml_time_unit time_unit,
			  double time_value)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_can_peek","connector_id = %d, time_unit = %d, time_value = %f",connector_id,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_can_peek,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id));
  EXIT_DEBUG_MSG("sn_bp_can_peek","result = %d",result);
  return result;
}


static int sn_bp_put_bitstream_request(unsigned         connector_id, 
				       unsigned         call_id, 
				       unsigned         callback_adapter_id, 
				       unsigned         stream_size, 
				       uvm_ml_stream_t  stream, 
				       uvm_ml_time_unit time_unit, 
				       double           time_value)
{ 
  int result = 0;
  ENTER_DEBUG_MSG("sn_bp_put_bitstream_request","connector_id = %d, call_id = %d, callback_adapter_id = %d, stream_size = %d, stream = %p, time_unit = %d, time_value = %f",
		  connector_id,call_id,callback_adapter_id,stream_size,stream,time_unit,time_value);
  SN_DISPATCH(sn_ml_put_bitstream_request,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,callback_adapter_id,stream_size,stream));
  EXIT_DEBUG_MSG("sn_bp_put_bitstream_request","result = %d",result);
  return result;
}

static int sn_bp_get_bitstream_request(unsigned connector_id, 
				       unsigned call_id, 
				       unsigned callback_adapter_id, 
				       uvm_ml_time_unit time_unit,
				       double time_value)
{
  int result = 0;
  ENTER_DEBUG_MSG("sn_bp_get_bitstream_request","connector_id = %d, call_id = %d, callback_adapter_id = %d, time_unit = %d, time_value = %f",
		  connector_id,call_id,callback_adapter_id,time_unit,time_value);
  SN_DISPATCH(sn_ml_get_bitstream_request,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,callback_adapter_id));
  EXIT_DEBUG_MSG("sn_bp_get_bitstream_request","result = %d",result);
  return result;
}
     
static int sn_bp_peek_bitstream_request(unsigned connector_id, 
					unsigned call_id, 
					unsigned callback_adapter_id,
					uvm_ml_time_unit time_unit,
					double time_value)
{  
  int result = 0;
  ENTER_DEBUG_MSG("sn_bp_peek_bitstream_request","connector_id = %d, call_id = %d, callback_adapter_id = %d, time_unit = %d, time_value = %f",
		  connector_id,call_id,callback_adapter_id,time_unit,time_value);
  SN_DISPATCH(sn_ml_peek_bitstream_request,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,callback_adapter_id));
  EXIT_DEBUG_MSG("sn_bp_peek_bitstream_request","result = %d",result);
  return result;
}

static int sn_bp_transport_bitstream_request(unsigned connector_id, 
					     unsigned call_id,
					     unsigned callback_adapter_id,
					     unsigned req_stream_size,
					     uvm_ml_stream_t req_stream,
					     unsigned * rsp_stream_size_ptr,
					     uvm_ml_stream_t rsp_stream,
					     uvm_ml_time_unit time_unit, 
					     double time_value)
{  
  int result = 0;
  ENTER_DEBUG_MSG("sn_bp_transport_bitstream_request","connector_id = %d, call_id = %d, callback_adapter_id = %d, req_stream_size = %d,req_stream = %p, rsp_stream_size_ptr = %p, rsp_stream = %p ,time_unit = %d, time_value = %f",
		  connector_id,call_id,callback_adapter_id,req_stream_size,req_stream,rsp_stream_size_ptr,rsp_stream,time_unit,time_value);
  SN_DISPATCH(sn_ml_transport_bitstream_request,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,callback_adapter_id,req_stream_size,req_stream));
  EXIT_DEBUG_MSG("sn_bp_transport_bitstream_request","result = %d",result);
  return result;
}

static unsigned sn_bp_get_requested_bitstream(unsigned connector_id,
					      unsigned call_id,
					      uvm_ml_stream_t stream) 
{
  unsigned int result;
  ENTER_DEBUG_MSG("sn_bp_get_requested_bitstream","connector_id = %d, call_id = %d, stream = %p",connector_id,call_id,stream);
  result = SN_DISPATCH(sn_ml_get_requested_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,stream));
  EXIT_DEBUG_MSG("sn_bp_get_requested_bitstream","result = %d",result);
  return result;
}

static unsigned sn_bp_peek_requested_bitstream(unsigned connector_id, 
					       unsigned call_id, 
					       uvm_ml_stream_t stream) 
{
  unsigned result;
  ENTER_DEBUG_MSG("sn_bp_peek_requested_bitstream","connector_id = %d, call_id = %d, stream = %p",connector_id,call_id,stream);
  result = SN_DISPATCH(sn_ml_peek_requested_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,stream));
  EXIT_DEBUG_MSG("sn_bp_peek_requested_bitstream","result = %d",result);
  return result;
}

static unsigned sn_bp_transport_response_bitstream(unsigned connector_id, 
						   unsigned call_id,
						   uvm_ml_stream_t rsp_stream) {
  unsigned result;
  ENTER_DEBUG_MSG("sn_bp_transport_response_bitstream","connector_id = %d, call_id = %d, rsp_stream = %p",connector_id,call_id,rsp_stream);
  result = SN_DISPATCH(sn_ml_get_requested_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,call_id,rsp_stream));
  EXIT_DEBUG_MSG("sn_bp_transport_response_bitstream","result = %d",result);
  return result;
}

static void sn_bp_turn_off_transaction_mapping(const char* socket_name) 
{
  ENTER_DEBUG_MSG("sn_bp_turn_off_transaction_mapping","socket_name = %s",socket_name);
  SN_DISPATCH(sn_ml_turn_transaction_mapping_off,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,socket_name));
  EXIT_DEBUG_MSG_VOID("sn_bp_turn_off_transaction_mapping");
}


static void sn_bp_notify_end_task(unsigned call_id,
				  uvm_ml_time_unit time_unit,
				  double time_value)
{
  ENTER_DEBUG_MSG("sn_bp_notify_end_task","call_id = %d, time_unit = %d, time_value = %f",call_id,time_unit,time_value);
  SN_DISPATCH(sn_ml_notify_end_task,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,call_id));
  EXIT_DEBUG_MSG_VOID("sn_bp_notify_end_task");
}

static int sn_bp_nb_transport_bitstream(unsigned connector_id,
					unsigned req_stream_size, 
					uvm_ml_stream_t req_stream,
					unsigned * rsp_stream_size_ptr,
					uvm_ml_stream_t rsp_stream,
					uvm_ml_time_unit time_unit, 
					double time_value)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_nb_transport_bitstream","connector_id = %d, req_stream_size = %d, req_stream = %p, rsp_stream_size_ptr = %p, rsp_stream = %p, time_unit = %d, time_value = %f",
		  connector_id,req_stream_size,req_stream,rsp_stream_size_ptr,rsp_stream,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_nb_transport_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,req_stream_size,req_stream,rsp_stream_size_ptr,rsp_stream));
  EXIT_DEBUG_MSG("sn_bp_nb_transport_bitstream","result = %d, *rsp_stream_size_ptr = %d",result,*rsp_stream_size_ptr);
  return result;
}

static void sn_bp_write_bitstream(unsigned connector_id,
				  unsigned stream_size,
				  uvm_ml_stream_t stream,
				  uvm_ml_time_unit time_unit, 
				  double time_value)
{
  ENTER_DEBUG_MSG("sn_bp_write_bitstream","connector_id = %d, stream_size= %d, stream = %p, time_unit = %d, time_value = %f",
		  connector_id,stream_size,stream,time_unit,time_value);
  SN_DISPATCH(sn_ml_write_bitstream,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,connector_id,stream_size,stream));
  EXIT_DEBUG_MSG_VOID("sn_bp_write_bitstream");
}

static int sn_bp_tlm2_b_transport_request(unsigned target_connector_id,
					  unsigned call_id, 
					  unsigned callback_adapter_id,
					  unsigned stream_size, 
					  uvm_ml_stream_t stream, 
					  uvm_ml_time_unit delay_unit, 
					  double delay_value,
					  uvm_ml_time_unit time_unit, 
					  double time_value)
{
  int result;
  SN_TYPE(real) time;
  ENTER_DEBUG_MSG("sn_bp_tlm2_b_transport_request","target_connector_id = %d, call_id = %d, callback_adapter_id = %d, stream_size = %d, stream = %p, delay_unit = %d, delay_value = %f, time_unit = %d, time_value = %f",
		  target_connector_id,call_id,callback_adapter_id,stream_size,stream,delay_unit,delay_value,time_unit,time_value);
  time = SN_REAL_NEW(delay_value);
  result = SN_DISPATCH(sn_ml_tlm2_b_transport_request,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,target_connector_id,call_id,callback_adapter_id,stream_size,stream,delay_unit,time));
  EXIT_DEBUG_MSG("sn_bp_tlm2_b_transport_request","result = %d",result);
  return result;
}

static int sn_bp_tlm2_b_transport_response(unsigned initiator_connector_id, 
					   unsigned call_id, 
					   unsigned *stream_size, 
					   uvm_ml_stream_t *stream)
{
  uvm_ml_tlm_sync_enum result;
  ENTER_DEBUG_MSG("sn_bp_tlm2_b_transport_response","initiator_connector_id = %d, call_id = %d, stream_size_ptr = %p, stream = %p",
		  initiator_connector_id,call_id,stream_size,stream);
  result = SN_DISPATCH(sn_bp_tlm2_b_transport_response,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,initiator_connector_id,call_id,stream_size,stream));
  EXIT_DEBUG_MSG("sn_bp_tlm2_b_transport_response","result = %d, *stream_size = %d ",result,*stream_size);
  return result;
}

static uvm_ml_tlm_sync_enum sn_bp_tlm2_nb_transport_fw(unsigned target_connector_id,
						       unsigned *stream_size, 
						       uvm_ml_stream_t *stream, 
						       uvm_ml_tlm_phase *phase,
						       unsigned transaction_id,
						       uvm_ml_time_unit *delay_unit,
						       double *delay_value,
						       uvm_ml_time_unit time_unit, 
						       double time_value)
{
  SN_TYPE(real) time;
  uvm_ml_tlm_sync_enum result;
  time = SN_REAL_NEW(*delay_value);
  ENTER_DEBUG_MSG("sn_bp_tlm2_nb_transport_fw","target_connector_id = %d, stream_size_ptr = %p, stream = %p, phase_ptr = %p, transaction_id = %d, delay_unit_ptr = %p, delay_value_ptr = %p, time_unit = %d, time_value = %f",
		  target_connector_id,stream_size,stream,phase,transaction_id,delay_unit,delay_value,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_tlm2_nb_transport_fw,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,target_connector_id,stream_size,stream,phase,transaction_id,delay_unit,&time));
  *delay_value = SN_REAL_GET(time);
  EXIT_DEBUG_MSG("sn_bp_tlm2_nb_transport_fw","result = %d,stream_size = %d,stream = %p, phase = %d, delay_unit = %d, delay_value = %f",
		 result,*stream_size,stream,*phase,*delay_unit,*delay_value);
  return result;
}

static uvm_ml_tlm_sync_enum sn_bp_tlm2_nb_transport_bw(unsigned target_connector_id, 
						       unsigned *stream_size, 
						       uvm_ml_stream_t *stream, 
						       uvm_ml_tlm_phase *phase,
						       unsigned transaction_id,
						       uvm_ml_time_unit *delay_unit,
						       double *delay_value,
						       uvm_ml_time_unit time_unit, 
						       double time_value)
{
  SN_TYPE(real) time;
  uvm_ml_tlm_sync_enum result;
  time = SN_REAL_NEW(*delay_value);
  ENTER_DEBUG_MSG("sn_bp_tlm2_nb_transport_bw","target_connector_id  = %d, stream_size_ptr = %p, stream = %p, phase_ptr = %p, transaction_id = %d, delay_unit_ptr = %p, delay_value_ptr = %p, time_unit = %d, time_value = %f",
		  target_connector_id,stream_size,stream,phase,transaction_id,delay_unit,delay_value,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_tlm2_nb_transport_bw,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,target_connector_id,stream_size,stream,phase,transaction_id,delay_unit,&time));
  *delay_value = SN_REAL_GET(time);
  EXIT_DEBUG_MSG("sn_bp_tlm2_nb_transport_bw","result = %d, stream_size = %d, stream = %p, phase = %d, delay_unit = %d, delay_value = %f",
		 result,*stream_size,stream,*phase,*delay_unit,*delay_value);
  return result;
}

static unsigned sn_bp_tlm2_transport_dbg(unsigned target_connector_id, 
					 unsigned *stream_size, 
					 uvm_ml_stream_t *stream,
					 uvm_ml_time_unit time_unit, 
					 double time_value)
{
  unsigned result;
  ENTER_DEBUG_MSG("sn_bp_tlm2_transport_dbg","target_connector_id = %d, stream_size_ptr = %p, stream = %p, time_unit  = %d, time_value = %f",
		  target_connector_id,stream_size,stream,time_unit,time_value);
  result = SN_DISPATCH(sn_ml_tlm2_transport_dbg,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,target_connector_id,stream_size,stream));
  EXIT_DEBUG_MSG("sn_bp_tlm2_transport_dbg","result = %d, stream_size = %d, stream = %p",result,stream_size,stream);
  return result;
}
  
static int sn_bp_create_child_junction_node(const char * component_type_name,
					    const char * instance_name,
					    const char * parent_full_name,
					    int          parent_framework_id,
					    int          parent_junction_node_id) 
{
  int result;
  SN_TYPE(string) component_type_name_copy = SN_STRING_NEW(strlen(component_type_name)+1);
  SN_TYPE(string) instance_name_copy = SN_STRING_NEW(strlen(instance_name)+1);
  SN_TYPE(string) parent_full_name_copy = SN_STRING_NEW(strlen(parent_full_name)+1);

  strcpy(component_type_name_copy,component_type_name);
  strcpy(instance_name_copy,instance_name);
  strcpy(parent_full_name_copy,parent_full_name);
  
  ENTER_DEBUG_MSG("sn_bp_create_child_junction_node","component_type_name = %s, instance_name = %s, parent_full_name = %s, parent_framework_id = %d, parent_junction_node_id = %d",
		  component_type_name,instance_name,parent_full_name,parent_framework_id,parent_junction_node_id);
  result = SN_DISPATCH(sn_ml_create_child,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,component_type_name_copy,instance_name_copy,parent_full_name_copy,parent_framework_id,parent_junction_node_id));
  EXIT_DEBUG_MSG("sn_bp_create_child_junction_node","result = %d",result);
  return result;
}

static int sn_bp_notify_phase(const char * phase_group,
			      const char * phase_name,
			      uvm_ml_phase_action phase_action) 
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_notify_phase","phase_group = %s, phase_name = %s, phase_action = %d",
		  phase_group,phase_name,phase_action);
  result = SN_DISPATCH(sn_ml_notify_phase,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,phase_group,phase_name,phase_action));
  EXIT_DEBUG_MSG("sn_bp_notify_phase","result = %d",result);
  return result;
}


static int sn_bp_transmit_phase(int child_component_id,
				const char * phase_group,
				const char * phase_name,
				uvm_ml_phase_action phase_action)
{
  int result;
  ENTER_DEBUG_MSG("sn_bp_transmit_phase","child_component_id = %d, phase_group = %s, phase_name = %s, phase_action = %d",
		  child_component_id,phase_group,phase_name,phase_action);
  result = SN_DISPATCH(sn_ml_transmit_phase,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,child_component_id,phase_group,phase_name,phase_action));
  EXIT_DEBUG_MSG("sn_bp_transmit_phase","result = %d",result);
  return result;
}

static void sn_bp_notify_config(const char *     cntxt,
				const char *     instance_name,
				const char *     field_name,
				unsigned int     stream_size,
				uvm_ml_stream_t  stream,
				uvm_ml_time_unit time_unit, 
				double           time_value) 
{
  /* Copy strings to Specman memory */
  SN_TYPE(string) cntxt_copy = SN_STRING_NEW(strlen(cntxt)+1);
  SN_TYPE(string) instance_name_copy = SN_STRING_NEW(strlen(instance_name)+1);
  SN_TYPE(string) field_name_copy = SN_STRING_NEW(strlen(field_name)+1);

  strcpy(cntxt_copy,cntxt);
  strcpy(instance_name_copy,instance_name);
  strcpy(field_name_copy,field_name);

  ENTER_DEBUG_MSG("sn_bp_notify_config","cntxt = %s, instance_name = %s, field_name = %s ",
		  cntxt,instance_name,field_name);

  SN_DISPATCH(sn_ml_notify_config,UVM_ML_ADAPTER,sn_ML_LIB_adapter,(UVM_ML_ADAPTER,cntxt_copy,instance_name_copy,field_name_copy,stream_size,stream));

  EXIT_DEBUG_MSG_VOID("sn_bp_notify_config");
}

/*                             */
/* Specman to Backplane calls  */
/*                             */

SN_TYPE(bool) ml_sn_has_get_pack_max_size_symbol() 
{
  SN_TYPE(bool) result;
  int (*bp_get_pack_max_size_ptr)() = 0; 
  ENTER_DEBUG_MSG_VOID("ml_sn_has_get_pack_max_size_symbol");
  bp_get_pack_max_size_ptr = dlsym(0,"bp_get_pack_max_size");
  result = bp_get_pack_max_size_ptr!=0;
  EXIT_DEBUG_MSG("ml_sn_has_get_pack_max_size_symbol","result = %d",result);
  return result;
}

int ml_sn_get_pack_max_size () 
{
  int result;
  ENTER_DEBUG_MSG_VOID("ml_sn_get_pack_max_size");
  result = provided_tray->get_pack_max_size_ptr(sn_uvm_ml_adapter_id);
  EXIT_DEBUG_MSG("ml_sn_get_pack_max_size","result = %d",result);
  return result;
}

void ml_sn_set_pack_max_size (int size) 
{
  ENTER_DEBUG_MSG("ml_sn_set_pack_max_size","size = %d",size);
  provided_tray->set_pack_max_size_ptr(sn_uvm_ml_adapter_id,size);
  EXIT_DEBUG_MSG_VOID("ml_sn_set_pack_max_size");
}

unsigned int ml_sn_assign_transaction_id() 
{
  unsigned int result;
  ENTER_DEBUG_MSG_VOID("ml_sn_assign_transaction_id");
  result = provided_tray->assign_transaction_id_ptr(sn_uvm_ml_adapter_id);
  EXIT_DEBUG_MSG("ml_sn_assign_transaction_id","result = %d");
  return result;
}

unsigned int ml_sn_get_type_id_from_name(char * type_name) 
{
  unsigned int result;
  ENTER_DEBUG_MSG("ml_sn_get_type_id_from_name","type_name = %s",type_name);
  result = provided_tray->get_type_id_from_name_ptr(sn_uvm_ml_adapter_id,type_name);
  EXIT_DEBUG_MSG("ml_sn_get_type_id_from_name","result = %d",result);
  return result;
}

SN_TYPE(string) ml_sn_get_type_name_from_id(unsigned int type_id) 
{
  SN_TYPE(string) result;
  ENTER_DEBUG_MSG("ml_sn_get_type_name_from_id","type_id = %d",type_id);
  result = provided_tray->get_type_name_from_id_ptr(sn_uvm_ml_adapter_id,type_id);
  EXIT_DEBUG_MSG("ml_sn_get_type_name_from_id","result = %d",result);
  return result;
}

unsigned int ml_sn_connect_names(SN_TYPE(string) path1,
				 SN_TYPE(string) path2) 
{
  unsigned int result;
  ENTER_DEBUG_MSG("ml_sn_connect_names","path1 = %s, path2 = %s",path1,path2);
  result = provided_tray->connect_ptr(sn_uvm_ml_adapter_id,path1,path2);
  EXIT_DEBUG_MSG("ml_sn_connect_names","result = %d",result);
  return result;
}

SN_TYPE(bool) ml_sn_can_get(unsigned int connector_id) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;

  ENTER_DEBUG_MSG("ml_sn_can_get","connector_id = %d",connector_id);
  result = provided_tray->can_get_ptr(sn_uvm_ml_adapter_id,connector_id,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_can_get","result = %d",result);
  return result;
}

SN_TYPE(bool) ml_sn_try_get_bitstream(unsigned int connector_id, 
				      unsigned int * clist_size,
				      void * clist0) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;

  ENTER_DEBUG_MSG("ml_sn_try_get_bitstream","connector_id = %d, clist_size_ptr = %p, clist = %p",
		  connector_id,clist_size,clist0);
  result = provided_tray->nb_get_ptr(sn_uvm_ml_adapter_id,connector_id,clist_size,clist0,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_try_get_bitstream","result = %d, clist_size = %d, clist = %p",result,*clist_size,clist0);
  return result;
}

SN_TYPE(bool) ml_sn_can_peek(unsigned int connector_id) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;

  ENTER_DEBUG_MSG("ml_sn_can_peek","connector_id = %d",connector_id);
  result = provided_tray->can_peek_ptr(sn_uvm_ml_adapter_id,connector_id,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_can_peek","result = %d",result);
  return result;
}

SN_TYPE(bool) ml_sn_try_peek_bitstream(unsigned int connector_id, 
				       unsigned int * clist_size, 
				       void * clist0) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;

  ENTER_DEBUG_MSG("ml_sn_try_peek_bitstream","connector_id = %d, clist_size_ptr = %p, clist = %p",
		  connector_id,clist_size,clist0);
  result = provided_tray->nb_peek_ptr(sn_uvm_ml_adapter_id,connector_id,clist_size,clist0,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_try_peek_bitstream","result = %d, clist_size = %d, clist = %p",result,*clist_size,clist0);
  return result;
}
    
SN_TYPE(bool) ml_sn_can_put(unsigned int connector_id) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;
  
  ENTER_DEBUG_MSG("ml_sn_can_put","connector_id = %d",connector_id);
  result = provided_tray->can_put_ptr(sn_uvm_ml_adapter_id,connector_id,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_can_put","result = %d",result);
  return result;
}

SN_TYPE(bool) ml_sn_try_put_bitstream(unsigned int connector_id,
				      unsigned int clist_size,
				      void * clist) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;
  
  ENTER_DEBUG_MSG("ml_sn_try_put_bitstream","connector_id = %d, clist_size = %d, clist = %p",
		   connector_id,clist_size,clist);
  result = provided_tray->nb_put_ptr(sn_uvm_ml_adapter_id,connector_id,clist_size,clist,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_try_put_bitstream","result = %d",result);
  return result;
}
    
void ml_sn_write_bitstream(unsigned int connector_id,
			   unsigned int clist_size, 
			   void * clist) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  
  ENTER_DEBUG_MSG("ml_sn_write_bitstream","connector_id = %d, clist_size = %d, clist = %p",
		  connector_id,clist_size,clist);
  provided_tray->write_ptr(sn_uvm_ml_adapter_id,connector_id,clist_size,clist,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG_VOID("ml_sn_write_bitstream");
}

void ml_sn_get_bitstream_request(unsigned int port_id, 
				 unsigned int call_id,
				 unsigned int * clist_size,
				 void * clist,
				 int * done) 
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  
  ENTER_DEBUG_MSG("ml_sn_get_bitstream_request","port_id = %d, call_id = %d, clist_size_ptr = %p, clist = %p, done_ptr = %p",
		  port_id,call_id,clist_size,clist,done);
  provided_tray->request_get_ptr(sn_uvm_ml_adapter_id,port_id,call_id,clist_size,clist,done,&dummy_time_unit,&dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_get_bitstream_request","clist_size = %d, done = %d",*clist_size,*done);
}

unsigned int ml_sn_get_requested_bitstream(unsigned int port_id,
					   unsigned int call_id,
					   void * stream)
{
  unsigned int result;

  ENTER_DEBUG_MSG("ml_sn_get_requested_bitstream","port_id = %d, call_id = %d, stream = %p",
		  port_id,call_id,stream);
  result = provided_tray->get_requested_ptr(sn_uvm_ml_adapter_id,port_id,call_id,stream);
  EXIT_DEBUG_MSG("ml_sn_get_requested_bitstream","result = %d",result);
  return result;
}

void ml_sn_peek_bitstream_request(unsigned int port_id,
				  unsigned int call_id,
				  unsigned int * clist_size,
				  void * clist, 
				  int * done)
{
  uvm_ml_time_unit dummy_time_unit = TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  
  ENTER_DEBUG_MSG("ml_sn_peek_bitstream_request","port_id = %d, call_id = %d, clist_size_ptr = %p, clist = %p, done_ptr = %p",
		  port_id,call_id,clist_size,clist,done);
  provided_tray->request_peek_ptr(sn_uvm_ml_adapter_id,port_id,call_id,clist_size,clist,done,&dummy_time_unit,&dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_peek_bitstream_request","clist_size = %d, done = %d",*clist_size,*done);
}

unsigned int ml_sn_peek_requested_bitstream(unsigned int port_id,
					    unsigned int call_id,
					    void * stream) 
{
  unsigned int result;

  ENTER_DEBUG_MSG("ml_sn_peek_requested_bitstream","port_id = %d, call_id = %d, stream = %p",
		  port_id,call_id,stream);
  result = provided_tray->peek_requested_ptr(sn_uvm_ml_adapter_id,port_id,call_id,stream);
  EXIT_DEBUG_MSG("ml_sn_peek_requested_bitstream","result = %d",result);
  return result;
}
    
void ml_sn_put_bitstream_request(unsigned int port_id,
				 unsigned int call_id,
				 unsigned int clist_size,
				 void * clist, 
				 int * done) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  
  ENTER_DEBUG_MSG("ml_sn_put_bitstream_request","port_id = %d, call_id = %d, clist_size = %d, clist = %p, done_ptr = %p",
		  port_id,call_id,clist_size,clist,done);
  provided_tray->request_put_ptr(sn_uvm_ml_adapter_id,port_id,call_id,clist_size,clist,done,&dummy_time_unit,&dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_put_bitstream_request","done = %d",*done);
}

SN_TYPE(bool) ml_sn_nb_transport_bitstream(unsigned int port_id, 
					   unsigned int req_clist_size, 
					   void * req_clist,
					   unsigned int * rsp_clist_size,
					   void * rsp_clist) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(bool) result;
  
  ENTER_DEBUG_MSG("ml_sn_nb_transport_bitstream","port_id = %d, req_clist_size = %d, req_clist_ptr = %p,	rsp_clist_size_ptr, rsp_clist = %p",
		  port_id,req_clist_size,req_clist,rsp_clist_size,rsp_clist);
  result = provided_tray->nb_transport_ptr(sn_uvm_ml_adapter_id,port_id,req_clist_size,req_clist,rsp_clist_size,rsp_clist,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_nb_transport_bitstream","result = %d,rsp_clist_size = %d",result,*rsp_clist_size);
  return result;
}

void ml_sn_transport_bitstream_request(unsigned int port_id,
				       unsigned int call_id,
				       unsigned int req_clist_size,
				       void * req_clist, 
				       unsigned int * rsp_clist_size,
				       void * rsp_clist,
				       int * done) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  
  ENTER_DEBUG_MSG("ml_sn_transport_bitstream_request","port_id = %d, call_id = %d, req_clist_size = %d, req_clist = %p, rsp_clist_size_ptr = %p, rsp_clist = %p, done_ptr = %p",
		  port_id,call_id,req_clist_size,req_clist,rsp_clist_size,rsp_clist,done);
  provided_tray->request_transport_ptr(sn_uvm_ml_adapter_id,port_id,call_id,req_clist_size,req_clist,rsp_clist_size,rsp_clist,done,&dummy_time_unit,&dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_transport_bitstream_request","rsp_clist_size = %d, done = %d",*rsp_clist_size,*done);
}


unsigned int ml_sn_transport_response_bitstream(unsigned int port_id,
						unsigned int call_id, 
						void * stream) 
{
  unsigned int result;
  
  ENTER_DEBUG_MSG("ml_sn_transport_response_bitstream","port_id = %d, call_id = %d, stream = %p",
		  port_id,call_id,stream);
  result = provided_tray->transport_response_ptr(sn_uvm_ml_adapter_id,port_id,call_id,stream);
  EXIT_DEBUG_MSG("ml_sn_transport_response_bitstream","result = %d",result);
  return result;
}

void ml_sn_notify_end_task(unsigned int adapter_cb_id, 
			   unsigned int call_id) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  
  ENTER_DEBUG_MSG("ml_sn_notify_end_task","adapter_cb_id = %d, call_id = %d",adapter_cb_id,call_id);
  provided_tray->notify_end_blocking_ptr(sn_uvm_ml_adapter_id,adapter_cb_id,call_id,dummy_time_unit,dummy_time_value);
  EXIT_DEBUG_MSG_VOID("ml_sn_notify_end_task");
}

int ml_sn_tlm2_b_transport_request(unsigned int initiator_connector_id,
				   unsigned int call_id,
				   unsigned int * stream_size,
				   void ** stream, 
				   SN_TYPE(e_time_units) delay_unit, 
				   SN_TYPE(real) delay_value, 
				   SN_TYPE(bool) * done) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  int result;
  double delay_value_d = SN_REAL_GET(delay_value);
  
  ENTER_DEBUG_MSG("ml_sn_tlm2_b_transport_request","initiator_connector_id = %d, call_id = %d, stream_size_ptr = %p, stream_ptr = %p, delay_unit = %d, delay_value = %f, done_ptr = %p",
		  initiator_connector_id,call_id,stream_size,stream,delay_unit,delay_value_d,done);
  result = provided_tray->request_b_transport_tlm2_ptr(sn_uvm_ml_adapter_id,
						       initiator_connector_id,
						       call_id,
						       stream_size,
						       (uvm_ml_stream_t *)stream,
						       delay_unit,
						       delay_value_d,
						       (unsigned int *)done,
						       dummy_time_unit,
						       dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_tlm2_b_transport_request","result = %d, stream_size = %d, done = %d",
		 result,*stream_size,*done);
  return result;
}

int ml_sn_tlm2_b_transport_response(unsigned int initiator_connector_id,
				    unsigned int call_id, 
				    unsigned int * stream_size,
				    void * stream) 
{
  int result;
  
  ENTER_DEBUG_MSG("ml_sn_tlm2_b_transport_response","initiator_connector_id = %d, call_id = %d, stream_size_ptr = %p, stream = %p",
		  initiator_connector_id,call_id,stream_size,stream);
  result = provided_tray->b_transport_tlm2_response_ptr(sn_uvm_ml_adapter_id,initiator_connector_id,call_id,stream_size,stream);
  EXIT_DEBUG_MSG("ml_sn_tlm2_b_transport_response","result = %d, stream_size = %d",result,*stream_size);
  return result;
}

SN_TYPE(tlm_sync_enum) ml_sn_tlm2_nb_transport_fw(unsigned int initiator_connector_id,
						  unsigned int * stream_size,
						  void ** stream,
						  SN_TYPE(tlm_phase_enum) * phase, 
						  int transaction_id, 
						  SN_TYPE(e_time_units) * delay_unit, 
						  void * delay_value) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(tlm_sync_enum) result;

  ENTER_DEBUG_MSG("ml_sn_tlm2_nb_transport_fw","initiator_connector_id = %d, stream_size_ptr = %p, stream_ptr = %p, phase_ptr = %p, transaction_id = %d, delay_unit_ptr = %p, delay_value_ptr = %p",
		  initiator_connector_id,stream_size,stream,phase,transaction_id,delay_unit,delay_value);
  result = provided_tray->nb_transport_fw_ptr(sn_uvm_ml_adapter_id,
					      initiator_connector_id,
					      stream_size,
					      (uvm_ml_stream_t *)stream,
					      (uvm_ml_tlm_phase *)phase,
					      transaction_id,
					      (uvm_ml_time_unit *)delay_unit,
					      (double *)delay_value,
					      dummy_time_unit,
					      dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_tlm2_nb_transport_fw","result = %d, stream_size = %d, phase = %d, delay_unit = %d, delay_value = %f",
		 result,*stream_size,*phase,(double *)delay_value);
  return result;
}

SN_TYPE(tlm_sync_enum) ml_sn_tlm2_nb_transport_bw(unsigned int initiator_connector_id,
						  unsigned int * stream_size, 
						  void ** stream,
						  SN_TYPE(tlm_phase_enum) * phase, 
						  int transaction_id,
						  SN_TYPE(e_time_units) * delay_unit,
						  void * delay_value) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  SN_TYPE(tlm_sync_enum) result;

  ENTER_DEBUG_MSG("ml_sn_tlm2_nb_transport_bw","initiator_connector_id = %d, stream_size_ptr = %p, stream_ptr = %p, phase_ptr = %p, transaction_id = %d, delay_unit_ptr = %p, delay_value_ptr = %p",
		  initiator_connector_id,stream_size,stream,phase,transaction_id,delay_unit,delay_value);
  result = provided_tray->nb_transport_bw_ptr(sn_uvm_ml_adapter_id,
					    initiator_connector_id,
					    stream_size,
					    (uvm_ml_stream_t *)stream,
					    (uvm_ml_tlm_phase *)phase,
					    transaction_id,
					    (uvm_ml_time_unit *)delay_unit,
					    (double *)delay_value,
					    dummy_time_unit,
					    dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_tlm2_nb_transport_bw","result = %d, phase = %d, delay_unit = %d, delay_value = %f",
		  result,*phase,*delay_unit,(double *)delay_value);
  return result;
}

unsigned int ml_sn_tlm2_transport_dbg(unsigned int initiator_connector_id,
				      unsigned int * stream_size,
				      void ** stream) 
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;
  unsigned int result;
  
  ENTER_DEBUG_MSG("ml_sn_tlm2_transport_dbg","initiator_connector_id = %d, stream_size_ptr = %p, stream_ptr = %p",
		  initiator_connector_id,stream_size,stream);
  result = provided_tray->transport_dbg_ptr(sn_uvm_ml_adapter_id,
					    initiator_connector_id,
					    stream_size,
					    (uvm_ml_stream_t *)stream,
					    dummy_time_unit,
					    dummy_time_value);
  EXIT_DEBUG_MSG("ml_sn_tlm2_transport_dbg","result = %d, stream_size = %d",result,*stream_size);
  return result;
}

void ml_sn_turn_transaction_mapping_off(SN_TYPE(string) socket_name) 
{ 
  ENTER_DEBUG_MSG("ml_sn_turn_transaction_mapping_off","socket_name = %s",socket_name);
  provided_tray->turn_off_transaction_mapping_ptr(sn_uvm_ml_adapter_id,socket_name);
  EXIT_DEBUG_MSG_VOID("ml_sn_turn_transaction_mapping_off");
}

void ml_sn_set_debug_mode(int mode) 
{
  ENTER_DEBUG_MSG("ml_sn_set_debug_mode","mode = %d",mode);
  provided_tray->set_trace_mode_ptr(mode);
  EXIT_DEBUG_MSG_VOID("ml_sn_set_debug_mode");
}

int ml_sn_get_connector_size(unsigned int connector_id) 
{
  int result;
  
  ENTER_DEBUG_MSG("ml_sn_get_connector_size","connector_id = %d",connector_id);
  result = provided_tray->get_connector_size_ptr(sn_uvm_ml_adapter_id,connector_id);
  EXIT_DEBUG_MSG_VOID("ml_sn_get_connector_size");
  return result;
}

void ml_sn_set_match_types(SN_TYPE(string) path1,
			   SN_TYPE(string) path2, 
			   SN_TYPE(string) path3) 
{
  ENTER_DEBUG_MSG("ml_sn_set_match_types","path1 = %s,path2 = %s,path3 = %s",path1,path2,path3);
  provided_tray->set_match_types_ptr(sn_uvm_ml_adapter_id,path1,path2);
  if (path3 != NULL && path3[0] != '\0')  {
    provided_tray->set_match_types_ptr(sn_uvm_ml_adapter_id,path1,path3);
  }
  EXIT_DEBUG_MSG_VOID("ml_sn_set_match_types");
}

int ml_sn_create_foreign_child(SN_TYPE(string) target_framework_name,
			       SN_TYPE(string) type_name, 
			       SN_TYPE(string) instance_name, 
			       SN_TYPE(string) parent_full_name,
			       int parent_component_id) 
{
  int result;
  ENTER_DEBUG_MSG("ml_sn_create_foreign_child","target_framework_name = %s,type_name = %s, instance_name = %s, parent_full_name = %s, parent_component_id = %d",
		  target_framework_name,type_name,instance_name,parent_full_name,parent_component_id);
  result = provided_tray->create_child_junction_node_ptr(sn_uvm_ml_adapter_id,
							 target_framework_name,
							 type_name,
							 instance_name,
							 parent_full_name,
							 parent_component_id);
  EXIT_DEBUG_MSG_VOID("ml_sn_create_foreign_child");
  if(result < 0) {
    printf("UVM-e adapter: Child component could not be created\n Framework: '%s' Type name: '%s' Parent name: '%s'\n", target_framework_name,type_name,parent_full_name);
  }
  return result;
}

int ml_sn_transmit_phase(SN_TYPE(string) phase_name,
			 SN_TYPE(string) phase_group,
			 SN_TYPE(uvm_ml_phase_action) phase_action,
			 SN_TYPE(string) target_framework_name,
			 int child_component_id)
{
  int result;
  
  ENTER_DEBUG_MSG("ml_sn_transmit_phase","phase_name = %s, phase_group = %s, phase_action = %d, target_framework_name = %s, child_component_id = %d",
		  phase_name,phase_group,phase_action,target_framework_name,child_component_id);
  result = provided_tray->transmit_phase_ptr(sn_uvm_ml_adapter_id,
					     target_framework_name, 
					     child_component_id,
					     phase_group,
					     phase_name,
					     phase_action);
  EXIT_DEBUG_MSG_VOID("ml_sn_transmit_phase");
  if(result <= 0) {
    printf("UVM-e adapter: Phase could not be propagated\n Framework: '%s' Phase: '%s'\n", target_framework_name,phase_name);
  }
  return result;
}

void ml_sn_notify_config(SN_TYPE(string) cntxt,
			 SN_TYPE(string) instance_name,
			 SN_TYPE(string) field_name,
			 unsigned int stream_size,
			 void * stream)
{
  uvm_ml_time_unit dummy_time_unit =  TIME_UNIT_UNDEFINED;
  double           dummy_time_value = 0;

  ENTER_DEBUG_MSG("ml_sn_notify_config","cntxt = %s, instance_name = %s, field_name = %s",
		  cntxt, instance_name, field_name);

  provided_tray->notify_config_ptr(sn_uvm_ml_adapter_id,
				   cntxt,
				   instance_name,
				   field_name,
				   stream_size,
				   stream,
				   dummy_time_unit,
				   dummy_time_value);

  EXIT_DEBUG_MSG_VOID("ml_sn_notify_config");

}

int ml_sn_get_adapter_id() 
{
  int result;
  ENTER_DEBUG_MSG_VOID("ml_sn_get_adapter_id");
  result = sn_uvm_ml_adapter_id;
  EXIT_DEBUG_MSG("ml_sn_get_adapter_id","result = %d",result);
  return result;
}

static void fill_bp_required_tray() 
{
  required_tray.set_trace_mode_ptr = sn_bp_set_debug_mode;
  required_tray.get_top_component_for_arg_ptr = sn_bp_get_top_component_for_arg;
  required_tray.startup_ptr = sn_bp_startup;
  required_tray.construct_top_ptr = sn_bp_add_top;
  required_tray.notify_phase_ptr = sn_bp_notify_phase;
  required_tray.transmit_phase_ptr = sn_bp_transmit_phase;
  required_tray.notify_runtime_phase_ptr = 0;
  required_tray.phase_srv_start_ptr = 0;
  required_tray.phase_srv_notify_phase_done_ptr = 0;

  required_tray.find_connector_id_by_name_ptr = sn_bp_find_connector_id_by_name;
  required_tray.get_connector_intf_name_ptr = sn_bp_get_connector_intf_name;
  required_tray.get_connector_type_ptr = sn_bp_get_connector_type;
  required_tray.is_export_connector_ptr = 0; 
  required_tray.try_put_uvm_ml_stream_ptr = sn_bp_try_put_bitstream;
  required_tray.can_put_ptr = sn_bp_can_put;
  required_tray.put_uvm_ml_stream_ptr = 0;
  required_tray.put_uvm_ml_stream_request_ptr = sn_bp_put_bitstream_request;
  required_tray.get_uvm_ml_stream_ptr = 0;
  required_tray.get_uvm_ml_stream_request_ptr = sn_bp_get_bitstream_request;
  required_tray.get_requested_uvm_ml_stream_ptr = sn_bp_get_requested_bitstream;
  required_tray.try_get_uvm_ml_stream_ptr = sn_bp_try_get_bitstream;
  required_tray.can_get_ptr = sn_bp_can_get;
  required_tray.peek_uvm_ml_stream_ptr = 0;
  required_tray.peek_uvm_ml_stream_request_ptr = sn_bp_peek_bitstream_request;
  required_tray.peek_requested_uvm_ml_stream_ptr = sn_bp_peek_requested_bitstream;
  required_tray.try_peek_uvm_ml_stream_ptr = sn_bp_try_peek_bitstream;
  required_tray.can_peek_ptr = sn_bp_can_peek;
  required_tray.transport_uvm_ml_stream_ptr = 0;
  required_tray.transport_uvm_ml_stream_request_ptr = sn_bp_transport_bitstream_request;
  required_tray.transport_response_uvm_ml_stream_ptr = sn_bp_transport_response_bitstream;
  required_tray.nb_transport_uvm_ml_stream_ptr = sn_bp_nb_transport_bitstream;
  required_tray.write_uvm_ml_stream_ptr = sn_bp_write_bitstream;
  required_tray.notify_end_blocking_ptr = sn_bp_notify_end_task;
  required_tray.tlm2_b_transport_ptr = 0;
  required_tray.tlm2_b_transport_request_ptr = sn_bp_tlm2_b_transport_request;
  required_tray.tlm2_b_transport_response_ptr = sn_bp_tlm2_b_transport_response;
  required_tray.tlm2_nb_transport_fw_ptr = sn_bp_tlm2_nb_transport_fw;
  required_tray.tlm2_nb_transport_bw_ptr = sn_bp_tlm2_nb_transport_bw;
  required_tray.tlm2_transport_dbg_ptr = sn_bp_tlm2_transport_dbg;
  required_tray.tlm2_turn_off_transaction_mapping_ptr = sn_bp_turn_off_transaction_mapping;
  required_tray.create_child_junction_node_ptr = sn_bp_create_child_junction_node;
  required_tray.notify_config_ptr = sn_bp_notify_config;
}

/* Linked list implementation */
static node * create_node(char *str) 
{
  node *result = (node *)malloc(sizeof(node));
  result->data = str;
  result->next = NULL;
  return result;
}

static void add_node(char *str) 
{
  node *ptr;
  node *new_node = create_node(str);

  if (!e_tops) {
    e_tops = new_node;
  } else {
    ptr = e_tops;
    while (ptr->next) {
      ptr=ptr->next;
    }
    ptr->next = new_node;
  }
}

static char * pop0_node_data() 
{
  char *result = NULL;
  node *ptr;

  if (e_tops) {
    result = e_tops->data;
    /* delete */
    ptr = e_tops;
    e_tops = e_tops->next;
    free(ptr);
  }

  return result;
}




