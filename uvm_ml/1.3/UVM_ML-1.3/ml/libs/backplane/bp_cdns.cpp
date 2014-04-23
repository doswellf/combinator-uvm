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

#include <iostream>
#include <vector>
#include <string>
#include "bp_common_c.h"
#include "bp_utils.h"
#include "bp_provided.h"
#include "bp_required.h"
#include "bp_interconnect.h"

using namespace std;
using namespace Bp;

extern "C" {
static bool unilang_backplane_initialized = false;
typedef struct unilang_api_struct 
{

    /* setup functions */

    /* unilang_reset_type * */ void * unilang_reset;
    /* unilang_set_debug_mode_type */ void *unilang_set_debug_mode;
    /* unilang_register_adapter_type */ void *unilang_register_adapter;
    /* unilang_register_adapter_sc_type */ void *unilang_register_adapter_sc;
    /* unilang_register_top_level_type */ void *unilang_register_top_level;
    /* unilang_connect_type */ void *unilang_connect;
    /* unilang_connect_names_type */ void *unilang_connect_names;

    /* put family */

    /* unilang_put_bitstream_type */ void  *unilang_put_bitstream;
    /* unilang_from_sv_put_bitstream_request_type */ void  *unilang_from_sv_put_bitstream_request;
    /* unilang_put_bitstream_request_type */ void  *unilang_put_bitstream_request;
    /* unilang_try_put_bitstream_type */ void  *unilang_try_put_bitstream;
    /* unilang_can_put_type */ void *unilang_can_put;

    /* unilang_ok_to_put_type */ void *unilang_ok_to_put;
    /* unilang_notify_ok_to_put_type */ void *unilang_notify_ok_to_put;

    /* get family */

    /* unilang_get_bitstream_type */ void  *unilang_get_bitstream;
    /* unilang_from_sv_get_bitstream_request_type  */ void *unilang_from_sv_get_bitstream_request;
    /* unilang_get_bitstream_request_type */ void  *unilang_get_bitstream_request;
    /* unilang_try_get_bitstream_type */ void  *unilang_try_get_bitstream;
    /* unilang_can_get_type */ void *unilang_can_get;
    /* unilang_get_requested_bitstream_type */ void  *unilang_get_requested_bitstream;

    /* unilang_peek_bitstream_type */ void  *unilang_peek_bitstream;
    /* unilang_from_sv_peek_bitstream_request_type */ void  *unilang_from_sv_peek_bitstream_request;
    /* unilang_peek_bitstream_request_type */ void  *unilang_peek_bitstream_request;
    /* unilang_try_peek_bitstream_type */ void  *unilang_try_peek_bitstream;
    /* unilang_can_peek_type */ void *unilang_can_peek;
    /* unilang_peek_requested_bitstream_type */ void  *unilang_peek_requested_bitstream;

    /* unilang_notify_end_task_type */ void *unilang_notify_end_task; // ??

    /* unilang_transport_bitstream_type */ void  *unilang_transport_bitstream;
    /* unilang_from_sv_transport_bitstream_request_type */ void  *unilang_from_sv_transport_bitstream_request;
    /* unilang_transport_bitstream_request_type */ void  *unilang_transport_bitstream_request;
    /* unilang_transport_response_bitstream_type */ void  *unilang_transport_response_bitstream;
    /* unilang_transport_bitstream_type */ void  *unilang_nb_transport_bitstream;

    /* analysis_if */

    /* unilang_write_bitstream_type */ void  *unilang_write_bitstream;

    /* unilang_get_connector_size_type */ void *unilang_get_connector_size;

    /* Max pack size query */

    /* unilang_get_pack_max_size_type */ void *unilang_get_pack_max_size;
    /* unilang_set_pack_max_size_type */ void *unilang_set_pack_max_size;

    /* unilang_get_tight_packing_mode_type */ void  *unilang_get_tight_packing_mode;
    /* unilang_set_tight_packing_mode_type */ void  *unilang_set_tight_packing_mode;

    /* hierarchical construction */
    /* unilang_create_component_type */ void              *unilang_create_component;
    /* unilang_connect_component_type */ void             *unilang_connect_component;
    /* unilang_end_of_elaboration_component_type */ void  *unilang_end_of_elaboration_component;
    /* unilang_start_of_simulation_component_type */ void  *unilang_start_of_simulation_component;
    /* unilang_run_component_type */ void                  *unilang_run_component;

    /* type id */
    /* unilang_get_type_id_from_name_type */ void         *unilang_get_type_id;
    /* unilang_get_type_name_from_id_type */ void         *unilang_get_type_name;         

    /* global time management */
    /* unilang_set_current_simulation_time_type */ void   *unilang_set_current_simulation_time;
    /* unilang_get_current_simulation_time_type */ void   *unilang_get_current_simulation_time;
  /* tlm2 */
  /* unilang_from_sv_tlm2_b_transport_type */ void          *unilang_from_sv_tlm2_b_transport;
  /* unilang_tlm2_b_transport_type */ void                  *unilang_tlm2_b_transport;
  /* unilang_from_sv_tlm2_b_transport_request_type */ void  *unilang_from_sv_tlm2_b_transport_request;
  /* unilang_tlm2_b_transport_request_type */ void          *unilang_tlm2_b_transport_request;
  /* unilang_from_sv_tlm2_b_transport_response_type */ void *unilang_from_sv_tlm2_b_transport_response;
  /* unilang_tlm2_b_transport_response_type */ void         *unilang_tlm2_b_transport_response;
  /* unilang_from_sv_tlm2_nb_transport_fw_type */ void      *unilang_from_sv_tlm2_nb_transport_fw;
  /* unilang_tlm2_nb_transport_fw_type */ void              *unilang_tlm2_nb_transport_fw;
  /* unilang_from_sv_tlm2_nb_transport_bw_type */ void      *unilang_from_sv_tlm2_nb_transport_bw;
  /* unilang_tlm2_nb_transport_bw_type */ void              *unilang_tlm2_nb_transport_bw;
  /* unilang_tlm2_transport_dbg_type */ void                *unilang_tlm2_transport_dbg; // No equivalent in SV yet

  /* tlm2 transaction id */
  /* unilang_assign_transaction_id_type */ void             *unilang_assign_transaction_id;
  /* unilang_set_transaction_mapping_type */ void           *unilang_set_transaction_mapping; 
} unilang_api_struct; 

static unilang_api_struct unilang_api;






unilang_api_struct * unilang_bootstrap
(
    bp_preInitial_t *preInitial,
    int              is_uvm,
    char **          uvmTops,
    char **          uvmTests,
    bp_serror_t *    serror
)
{
    vector<string> tops;

    if (getenv("UNILANG_DEBUG_MODE"))
        BpInterconnect::SetTraceMode(1);

    if (uvmTops) 
    {
        char * top;
        for (int j = 0; (top = uvmTops[j]) && *(top); j++)
            tops.push_back(string(top));
    }

    vector<string> tests;
    if (uvmTests) 
    {
        char * test;
        for (int j = 0; (test = uvmTests[j]) && *(test); j++)
            tests.push_back(string(test));
    }

    bp_api_struct * bp_api = BpInterconnect::Bootstrap(preInitial, tops, tests, serror);

    unilang_backplane_initialized = true;
    memset(&unilang_api, 0, sizeof(unilang_api_struct));
    return &unilang_api;
}
}
