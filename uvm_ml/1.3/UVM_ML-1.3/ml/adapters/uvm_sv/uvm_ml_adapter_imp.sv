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

`define uvm_ovm_(body)          uvm_``body
`define UVM_OVM_(body)          UVM_``body
`define UVM_OVM_MACRO_(body)   `UVM_``body
`define uvm_ovm_literal_(body) `"uvm_``body`"
`define uvm_ovm_TLM_(body)     `UVM_TLM_``body     

package uvm_ml_adapter_imp;

import `uvm_ovm_(pkg)::*;
`include "uvm_macros.svh"
`include "uvm_ml_common.svh"
`include "uvm_ml_import_dpi.svh"
`include "uvm_ml_serial.svh"
`include "uvm_ml_tlm1.svh"
`include "uvm_ml_tlm2.svh"
`include "uvm_ml_blocking_helper.svh"
`include "uvm_ml_phase_participate_handler.svh"
`include "uvm_ml_phase.svh"
`include "uvm_ml_phase_service.svh"
`include "uvm_ml_hierarchy.svh"
`include "uvm_ml_resource.svh"
`include "uvm_ml_export_dpi.svh"

endpackage

`define UVM_ML_REGISTER_B_SCKT(KIND) \
  uvm_tlm_b_``KIND``_socket_base #(TRAN_T) tmp; \
  $cast(tmp,sckt); \
  register_b_``KIND``(tmp);

`define UVM_ML_REGISTER_NB_SCKT(KIND) \
  uvm_tlm_nb_``KIND``_socket_base #(TRAN_T,P) tmp; \
  $cast(tmp,sckt); \
  register_nb_``KIND``(tmp);
