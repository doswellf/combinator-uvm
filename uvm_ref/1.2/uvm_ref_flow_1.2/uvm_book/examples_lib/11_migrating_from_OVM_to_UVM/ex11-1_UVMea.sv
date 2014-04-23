/****************************************************************
  Example 11-1: UVM Testbench Migration : UVM1.0 EA Design

  To run:   %  irun -uvm ex11-1_UVMea.sv
****************************************************************/
import uvm_pkg::*;
`include "uvm_macros.svh"

class myitem extends uvm_sequence_item;
  function new(string name="myitem");
    super.new(name);
  endfunction
  `uvm_object_utils(myitem)
endclass

typedef class myseqr;

class myseq extends uvm_sequence#(myitem);
  `uvm_sequence_utils(myseq, myseqr)

  task body;
    myitem item;
    for (int i=0; i<p_sequencer.cnt; ++i) begin
      p_sequencer.uvm_report_info("SEND",
         $sformatf("Sending item:%s", item.sprint()),
         UVM_MEDIUM);
      `uvm_do(item)
    end
  endtask
endclass

class myseqr extends uvm_sequencer#(myitem);
  `uvm_sequencer_utils(myseqr)
  function new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_update_sequence_lib_and_item(myitem)
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
  function void build();
    super.build();
    //monitor = mymonitor::type_id::create("monitor",this);
    if(is_active == UVM_ACTIVE) begin
      seqr = myseqr::type_id::create("seqr",this);
      driver = mydriver::type_id::create("driver",this);
    end
  endfunction
  function void connect();
    super.connect();
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

  function void build();
    super.build();
    set_config_string("agent.seqr", "default_sequence", "uvm_exhaustive_sequence");
    agent = myagent::type_id::create("agent",this);
  endfunction
endclass
