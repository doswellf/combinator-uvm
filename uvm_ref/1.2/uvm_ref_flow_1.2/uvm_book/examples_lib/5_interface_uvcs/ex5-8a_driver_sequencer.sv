/**************************************************************************
  Example: Simple Driver/Sequencer interaction

  To run:   %  irun -uvm ex5-8a_driver_sequencer.sv

  OR:       %  irun -uvmhome $UVM_HOME ex5-8a_driver_sequencer.sv
**************************************************************************/
module test;
   import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Simple request item that contains one field, question
  class simple_transfer extends uvm_sequence_item;
    rand int question;
    int answer;
    `uvm_object_utils_begin(simple_transfer)
      `uvm_field_int(question, UVM_DEFAULT)
      `uvm_field_int(answer, UVM_DEFAULT)
    `uvm_object_utils_end
    function new (string name="simple_transfer");
      super.new(name);
    endfunction : new
  endclass : simple_transfer

  class simple_seq  extends uvm_sequence #(simple_transfer);
    `uvm_object_utils(simple_seq)

    function new (string name="simple_seq");
      super.new(name);
    endfunction : new

    virtual task body();
      starting_phase.raise_objection(this, "simple_seq");
      `uvm_do(req)
      starting_phase.drop_objection(this, "simple_seq");
    endtask : body

  endclass : simple_seq

  class simple_sequencer  extends uvm_sequencer #(simple_transfer);
    `uvm_component_utils(simple_sequencer)
    function new (string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new
  endclass

  class simple_driver extends uvm_driver #(simple_transfer);
    function new (string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new
    `uvm_component_utils(simple_driver)

    task run_phase(uvm_phase phase);
      get_and_drive();
    endtask : run_phase

task get_and_drive();
  while (1) begin
    seq_item_port.get_next_item(req);
    send_to_dut(req);
    seq_item_port.item_done();
  end
endtask

task send_to_dut(simple_transfer trans);
  // Logic to handle sending multiple data items in flight
  trans.answer = trans.question + 1;
  trans.print();
endtask : send_to_dut

endclass

  simple_sequencer  s_sequencer0;
  simple_driver s_driver0;

  initial begin
    `uvm_info("TOP", "Beginning test...", UVM_LOW)
    uvm_config_string::set(null, "s_sequencer0.run_phase", "default_sequence", "simple_seq");
    s_sequencer0 = new("s_sequencer0", null); s_sequencer0.build_phase(null);
    s_driver0 = new("s_driver0", null); s_driver0.build_phase(null);
    s_driver0.seq_item_port.connect(s_sequencer0.seq_item_export);
    s_driver0.rsp_port.connect(s_sequencer0.rsp_export);
    s_sequencer0.print(); s_driver0.print();
    run_test();
  end 

  initial begin
    #10000;
    global_stop_request();
  end

endmodule
