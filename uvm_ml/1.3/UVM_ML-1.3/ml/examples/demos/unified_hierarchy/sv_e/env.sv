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

typedef enum {FALSE,TRUE} boolean;

  // The environment contains one instance of the producer and 
  // one instance of the consumer
  class sv_env extends uvm_env;
    producer prod;
    consumer cons;
    boolean e_active;
    boolean sv_active;

    `uvm_component_utils_begin(sv_env)
       `uvm_field_enum(boolean, e_active, UVM_DEFAULT)
       `uvm_field_enum(boolean, sv_active, UVM_DEFAULT)
    `uvm_component_utils_end
      
    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      `uvm_info(get_type_name(),$sformatf("SV sv_env::new %s", name),UVM_LOW);
    endfunction

    function void build_phase(uvm_phase phase);
      bit res;      
      super.build_phase(phase);
      `uvm_info(get_type_name(),$sformatf("SV sv_env::build"),UVM_LOW);
      
      if(sv_active) begin
	 prod = producer::type_id::create("producer", this);
      end;
      if(e_active) begin
	 cons = consumer::type_id::create("consumer", this);
      end;
    endfunction
   
  endclass
