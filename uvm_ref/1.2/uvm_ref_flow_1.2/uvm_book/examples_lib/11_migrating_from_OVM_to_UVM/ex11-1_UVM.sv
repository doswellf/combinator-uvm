/****************************************************************
  Example 11-1a: UVM Testbench Migration : UVM1.0 Migrated

  To run:   %  irun -uvm ex11-1_UVM.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"

//----------------------------------------------
// UVM1.1
//----------------------------------------------
class myitem extends uvm_sequence_item;
  function new(string name="myitem");
    super.new(name);
  endfunction
  `uvm_object_utils(myitem)
endclass

typedef class myseqr;
typedef uvm_sequence_library#(myitem) myseq_lib;

class myseq extends uvm_sequence#(myitem);
  `uvm_object_utils(myseq)
  `uvm_declare_p_sequencer(myseqr)
  `uvm_add_to_seq_lib(myseq, myseq_lib)

  task body;
    myitem item;
    for (int i=0; i<p_sequencer.cnt; ++i) begin
      `uvm_info("SEND",
         $sformatf("Sending item:%s", item.sprint()),
         UVM_MEDIUM)
      `uvm_do(item)
    end
  endtask
endclass

class myseqr extends uvm_sequencer#(myitem);
  `uvm_component_utils(myseqr)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction 
  rand int cnt = 10;
endclass

class mydriver extends uvm_driver#(myitem);
  `uvm_component_utils(mydriver)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction 
  rand int cnt = 10;
endclass

class myagent extends uvm_agent;
  myseqr seqr;
  mydriver driver;
  //mymonitor  monitor;
  `uvm_component_utils(myagent)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction 
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //monitor = mymonitor::type_id::create("monitor",this);
    if(is_active == UVM_ACTIVE) begin
      seqr = myseqr::type_id::create("seqr",this);
      driver = mydriver::type_id::create("driver",this);
    end
  endfunction
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(seqr.seq_item_export);
    end
  endfunction
endclass

class test extends uvm_component;
  `uvm_component_utils(test)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction 

  myagent agent;
  myseq_lib slib;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    slib = myseq_lib::type_id::create("slib", this);
    slib.selection_mode = UVM_SEQ_LIB_RANDC;
    void'(slib.randomize());
    uvm_config_seq::set(this, "agent.seqr.run_phase", "default_sequence", slib);
    agent = myagent::type_id::create("agent",this);
  endfunction
endclass
