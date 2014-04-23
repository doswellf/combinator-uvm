/**************************************************************************
  Example 5-9: Simple Driver for Pipeline Protocol

  To run:   %  irun -uvm ex5-9_simple_pipe_driver.sv
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

class simple_sequencer  extends uvm_sequencer #(simple_transfer);
  `uvm_component_utils(simple_sequencer)
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
endclass

class pipeline_seq extends uvm_sequence;
  simple_transfer s_req_list [$];
  rand int unsigned num_s_req;
  rand simple_transfer s_req;
  rand int unsigned num_p_req;
    constraint c_num_p_req { num_p_req inside {1,2,3,4}; }
    constraint c_num_s_req { num_s_req inside {1,2,3,4}; }

  int unsigned delay_p_req;
  int unsigned delay_s_req;

  function new(string name="pipeline_seq");
    super.new(name);
  endfunction
  `uvm_object_utils_begin(pipeline_seq)
    `uvm_field_int(num_s_req, UVM_DEFAULT)
    `uvm_field_queue_object(s_req_list, UVM_DEFAULT)
  `uvm_object_utils_end

  virtual task body();
    `uvm_info("pipeline_seq", "Starting...", UVM_LOW)
    #10;
    fork
      send_requests();
      process_responses();
    join
  endtask

  function void post_do(uvm_sequence_item this_item);
    uvm_sequence_item temp_item;
    simple_transfer t_s_req;
    $cast(temp_item, this_item.clone());
    temp_item.set_id_info(this_item);
    if($cast(t_s_req, temp_item))
      s_req_list.push_front(t_s_req);
    else
      `uvm_error("CASTFAIL", "ERROR!")
  endfunction

  task send_requests();
    `uvm_info("send_requests", $sformatf("%0d s_req items will be sent.", num_s_req), UVM_LOW)
    for(int i = 0; i < num_s_req; i++) begin
      assert(std::randomize(delay_s_req) with { delay_s_req < 200; });
      #delay_s_req;
      `uvm_info("send_requests", $sformatf("Sending s_req #%0d...", i), UVM_LOW)
      `uvm_do(s_req)
    end
  endtask

  task process_responses();
    uvm_sequence_item t_uvs;
    simple_transfer temp_s_req;
    simple_transfer temp_s_rsp;
    for (int i = 0; i < num_s_req + num_p_req; i++) begin
      get_response(t_uvs);
      if ($cast(temp_s_rsp, t_uvs)) begin  // is simple_transfer
        for (int i = 0; i < s_req_list.size(); i++) begin
          if(temp_s_rsp.get_transaction_id() == s_req_list[i].get_transaction_id())
            assert(temp_s_rsp.answer == s_req_list[i].question + 1) begin
              `uvm_info("process_responses", $sformatf("Simple Request/Response pair for...\n%s\n%s", s_req_list[i].sprint(), temp_s_rsp.sprint()), UVM_LOW)
              s_req_list.delete(i);
            end
            else
              `uvm_error("process_responses", "ERROR -- simple question answer mismatch")
        end
      end
      else
       `uvm_error("process_responses", "ERROR -- unexpected response type")
    end
  endtask

  virtual task pre_body();
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence '",
                                            get_full_name(), "'"});
  endtask

  virtual task post_body();
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence '",
                                           get_full_name(), "'"});
  endtask

endclass : pipeline_seq

class simple_driver extends uvm_driver #(simple_transfer);
  simple_transfer req_list [$];
  int max_pipeline_depth=2;
  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
  `uvm_component_utils_begin(simple_driver)
    `uvm_field_int(max_pipeline_depth, UVM_DEFAULT)
    `uvm_field_queue_object(req_list, UVM_DEFAULT)
  `uvm_component_utils_end

  task run_phase(uvm_phase phase);
    fork
      get_and_drive();
      drive_transfers();
    join
  endtask : run_phase

task get_and_drive();
  while (req_list.size() < max_pipeline_depth) begin
    seq_item_port.get_next_item(req);
    `uvm_info("get_and_drive", {"has a req\n", req.sprint()}, UVM_LOW)
    $cast(rsp, req.clone());
    rsp.set_id_info(req);
    req_list.push_front(rsp);
    seq_item_port.item_done();
  end
endtask : get_and_drive

task drive_transfers();
  simple_transfer cur_req;
  while (1) begin
    wait (req_list.size()>0)
    cur_req = req_list.pop_back();
    send_to_dut(cur_req);
    rsp_port.write(cur_req);
  end
endtask : drive_transfers

task send_to_dut(simple_transfer trans);
  // Logic to handle sending multiple data items in flight
  trans.answer = trans.question + 1;
endtask : send_to_dut

endclass

class simple_test extends uvm_test;
  simple_sequencer  sequencer;
  simple_driver driver;

  `uvm_component_utils(simple_test)

  function new(string name="simple_test", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "sequencer.run_phase", "default_sequence", pipeline_seq::get_type());
    sequencer = simple_sequencer::type_id::create("sequencer", this);
    driver    = simple_driver::type_id::create("driver", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
    driver.rsp_port.connect(sequencer.rsp_export);
  endfunction : connect_phase

  function void start_of_simulation_phase(uvm_phase phase);
    this.print();
    //uvm_test_done.set_drain_time(this, 100);
  endfunction : start_of_simulation_phase
endclass : simple_test

  initial begin
    `uvm_info("TOP", "Beginning test...", UVM_LOW)
  //  run_test("simple_test");
  end 

endmodule
