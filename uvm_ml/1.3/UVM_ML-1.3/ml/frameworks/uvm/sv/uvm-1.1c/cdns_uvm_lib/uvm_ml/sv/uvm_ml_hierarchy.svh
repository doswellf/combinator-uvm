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

// /////////////////////////////////
//
// ML Hierarchy
//
// /////////////////////////////////

typedef class child_component_proxy;

class child_component_proxy extends uvm_component;

    int    m_parent_id;

    string m_target_frmw_ind;
    string m_component_type_name;
    int    m_child_junction_node_id;
            
    function new(string name, uvm_component parent);

        super.new(name, parent);
    endfunction : new

    // return -1 for failure
    function int create_foreign_child_junction_node(string target_frmw_ind, 
                                                    string component_type_name);
        uvm_component p;

        p = get_parent();

        //assert (p != null);
        if(p == null) begin
           string msg;
	   $swrite(msg, 
		   "UVM-SV adapter: cannot find the parent of child junction node %s", component_type_name);
	   `uvm_ovm_(report_error) ("MLCRTCOMP", msg);
	   return -1;
        end;
      

        m_parent_id = get_hierarchical_node_id(p);
        m_target_frmw_ind = target_frmw_ind;
        m_component_type_name = component_type_name;

        m_child_junction_node_id  = uvm_ml_create_child_junction_node(m_target_frmw_ind, 
                                                                      m_component_type_name,
                                                                      get_name(),
                                                                      p.get_full_name(),
                                                                      m_parent_id);
        return m_child_junction_node_id; // (-1) if uvm_ml_create_child_junction_node failed
    endfunction : create_foreign_child_junction_node

    function void phase_started(uvm_phase phase);
        uvm_domain domain = phase.get_domain();
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, domain.get_name(), phase.get_name(), UVM_ML_PHASE_STARTED);
    endfunction

    function void phase_ended(uvm_phase phase);
        uvm_domain domain = phase.get_domain();
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, domain.get_name(), phase.get_name(), UVM_ML_PHASE_ENDED);
    endfunction

    function void phase_ready_to_end(uvm_phase phase);
        uvm_domain domain = phase.get_domain();
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, domain.get_name(), phase.get_name(), UVM_ML_PHASE_READY_TO_END);
    endfunction

    function void build_phase(uvm_phase phase);
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, "common", "build", UVM_ML_PHASE_EXECUTING);
    endfunction

    function void connect_phase(uvm_phase phase);
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, "common", "connect", UVM_ML_PHASE_EXECUTING);
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, "common", "end_of_elaboration", UVM_ML_PHASE_EXECUTING);
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, "common", "start_of_simulation", UVM_ML_PHASE_EXECUTING);
    endfunction

    function void resolve_bindings();
        int res = uvm_ml_transmit_phase(m_target_frmw_ind, m_child_junction_node_id, "common", "resolve_bindings", UVM_ML_PHASE_EXECUTING);
    endfunction

    `uvm_component_utils(child_component_proxy)      
endclass : child_component_proxy


function uvm_component create_component(string        target_framework_indicator, 
                                        string        component_type_name, 
                                        string        instance_name,
                                        uvm_component parent);
    int result;
    child_component_proxy child_proxy;
      
    child_proxy = new (instance_name,parent);
    result = child_proxy.create_foreign_child_junction_node(target_framework_indicator, component_type_name);
    if (result < 0) begin
        `uvm_ovm_(report_fatal)("MLCRTCOMP", {"UVM-SV adapter: Could not create foreign language ", 
                                              target_framework_indicator, 
                                              "component of type ", component_type_name, 
                                              " in uvm_ml_create_component"}
                               );
        return null;
    end
    else
        return child_proxy;
endfunction : create_component

// //////////////////////
//
// Parent proxy 
//
// //////////////////////
  
class parent_proxy extends uvm_component;
    uvm_component child_list[$];      
    int           m_numChildren; // Number of Child Junction Nodes
            
    function new(string name, uvm_component parent);

      uvm_component m_proxy;
      bit           i;
      string        component_type_name;
      string        instance_name;
      string        parent_full_name;

      super.new(name, parent);
      
      i = get_config_string("uvm_ml_type_name", component_type_name);
      i = get_config_string("uvm_ml_inst_name", instance_name);
      i = get_config_string("uvm_ml_parent_name", parent_full_name);

      m_proxy = factory.create_component_by_name(component_type_name, "", instance_name, this);

      child_list.push_back(m_proxy);
      m_numChildren = 1;
    endfunction : new
      
    function void add_node(int proxyId, string component_type_name, string instance_name, string parent_full_name);
      child_list[m_numChildren] = factory.create_component_by_name(component_type_name, "", instance_name, this);
      m_numChildren = m_numChildren+1;
    endfunction : add_node

    `uvm_component_utils(parent_proxy)

    virtual function int unsigned get_depth();
      int current_depth;
      current_depth = -1;
      if (get_config_int("uvm_ml_current_depth", current_depth)) begin
        if (current_depth != (-1))
          return current_depth;
      end
      return uvm_component::get_depth();
    endfunction : get_depth

    static function bit compare_prefix(string full_name, string prefix);
        assert (prefix.len() <= full_name.len());
        for (int i = 0; i < prefix.len(); i++) begin
            if (prefix[i] != full_name[i]) // Case sensitive comparison
            return 0;
        end
        return 1;
    endfunction : compare_prefix

    static parent_proxy parent_proxies[$];
    static int parent_proxy_ids[$];
    static string proxy_names[$];
    static int proxy_tops[$];
    static int num_proxies;

    static function int create_parent_proxy(string component_type_name, 
                                            string instance_name,
                                            string parent_full_name,
                                            int    parent_framework_id,
                                            int    parent_junction_node_id);
        parent_proxy p;
        int top;
        string proxy_name;
        proxy_name = {component_type_name,"_proxy"};
          
        for(int i = 0; i<num_proxies; i++) begin
            if(proxy_names[i] == parent_full_name) begin
	        parent_proxies[i].add_node(parent_junction_node_id, component_type_name, instance_name, parent_full_name);
                return get_hierarchical_node_id(parent_proxies[i].child_list[$]);
	    end
        end
      
        // Does not work for one simulator: uvm_config_string::set(uvm_root::get(), "*", "uvm_ml_type_name", component_type_name);
        uvm_extended_string_config_db::set(uvm_root::get(), "*", "uvm_ml_type_name", component_type_name);
        // uvm_config_string::set(uvm_root::get(), "*", "uvm_ml_inst_name", instance_name);
        uvm_extended_string_config_db::set(uvm_root::get(), "*", "uvm_ml_inst_name", instance_name);
        // uvm_config_string::set(uvm_root::get(), "*", "uvm_ml_parent_name", parent_full_name);
        uvm_extended_string_config_db::set(uvm_root::get(), "*", "uvm_ml_parent_name", parent_full_name);
      
        $cast(p, factory.create_component_by_name("parent_proxy", parent_full_name, parent_full_name, null));
        top = uvm_top.top_levels.size()-1;
            
        parent_proxies.push_back(p);
        parent_proxy_ids.push_back(parent_junction_node_id);
        proxy_tops.push_back(top);
        proxy_names.push_back(parent_full_name);
        num_proxies++;
      
        return get_hierarchical_node_id(parent_proxies[$].child_list[$]);
    endfunction : create_parent_proxy

    static function parent_proxy find_proxy_for_accessor(string cntxt);
        parent_proxy result;
        parent_proxy c_proxy;
        int unsigned longest_match_length;
        string       s;
        int          len;

        for (int i = 0; i< num_proxies; i++) begin
            c_proxy = parent_proxies[i];
            s = c_proxy.get_full_name();
            len = s.len();

            if (len > longest_match_length && compare_prefix(c_proxy.get_full_name(), cntxt)) begin
                // the longest match found
                longest_match_length = len;
                result = c_proxy;
            end
        end
        return result;
    endfunction : find_proxy_for_accessor

endclass : parent_proxy

