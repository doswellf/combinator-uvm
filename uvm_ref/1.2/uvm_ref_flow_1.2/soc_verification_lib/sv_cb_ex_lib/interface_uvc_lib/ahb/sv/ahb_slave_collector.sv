/*******************************************************************************
  FILE : ahb_slave_collector.sv
*******************************************************************************/
//   Copyright 1999-2010 Cadence Design Systems, Inc.
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

`ifndef AHB_SLAVE_COLLECTOR_SV
`define AHB_SLAVE_COLLECTOR_SV

//------------------------------------------------------------------------------
// CLASS: ahb_slave_collector
//--

class ahb_slave_collector extends uvm_component;

// The virtual interface used to view HDL signals

virtual interface ahb_if vif;

// Property indicating the number of transactions occuring on the ahb.
  protected int unsigned num_transactions = 0;

// TLM Ports - transfer collected for monitor other components
  uvm_analysis_port #(ahb_transfer) item_collected_port;
 
// The following property holds the transaction information currently
  // being captured (by the collect_address_phase and data_phase methods). 
  ahb_transfer trans_collected;

// Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(ahb_slave_collector)
    `uvm_field_int(num_transactions, UVM_DEFAULT)
  `uvm_component_utils_end


 // new - constructor
  function new (string name, uvm_component parent);
    super.new(name, parent);
    trans_collected = ahb_transfer::type_id::create("trans_collected");
    // TLM ports are created here
    item_collected_port = new("item_collected_port", this);
  endfunction : new

 // Additional class methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern virtual protected task collect_response();
  extern virtual function void report_phase(uvm_phase phase);

endclass : ahb_slave_collector

// UVM build_phase
function void ahb_slave_collector::build_phase(uvm_phase phase);
    super.build_phase(phase);
endfunction : build_phase

// UVM connect_phase
function void ahb_slave_collector::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_error("NOVIF", {"virtual interface must be set for: ", get_full_name(), ".vif"})
endfunction : connect_phase


// UVM run_phase()
task ahb_slave_collector::run_phase(uvm_phase phase);
   fork
    collect_response();
   join
endtask : run_phase

// collect_response
task ahb_slave_collector::collect_response();

// This collector re-uses its data item for ALL transfers
    forever begin
      @(posedge vif.ahb_clock iff vif.AHB_HREADY === 1);
      // Enable transfer recording
      void'(begin_tr(trans_collected, "AHB SLAVE Collector"));
      trans_collected.data = vif.AHB_HWDATA;
      @(posedge vif.ahb_clock);
      end_tr(trans_collected);
      `uvm_info(get_type_name(),
        $sformatf("slave transfer collected :\n%s",
        trans_collected.sprint()), UVM_HIGH)
      
    // Send transfer to scoreboard via TLM write()
      item_collected_port.write(trans_collected);
      num_transactions++;
    end
  endtask : collect_response

function void ahb_slave_collector::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Report: AHB slave collector collected %0d transfers", num_transactions), UVM_LOW);
endfunction : report_phase

`endif // AHB_SLAVE_COLLECTOR_SV
