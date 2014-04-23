/*----------------------------------------------------------------------
 Chapter 8 - Stimulus Generation Topics - Sequence Layering
  Example: Layering inside one sequencer
  
  To run:  %  irun -uvm ex8-2a_single_layer_arch.sv
----------------------------------------------------------------------*/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"
`define DATA_SIZE 8
`define MAX_PL 10

// Lower-Env Item
class lower_env_item extends uvm_sequence_item;
  rand bit [`DATA_SIZE-1:0] payload[];
  rand int unsigned pl_size;
  constraint pload_cst { pl_size < `MAX_PL;
                         payload.size() == pl_size; }

  `uvm_object_utils_begin(lower_env_item)
     `uvm_field_array_int(payload, UVM_DEFAULT)
     `uvm_field_int(pl_size, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end
 
  function new (string name="lower_env_item");
    super.new(name);
  endfunction : new

endclass : lower_env_item

// Upper-Env Item - composed of multiple lower_env_item's
class upper_env_item extends uvm_sequence_item;
  rand int unsigned max_item_size;
  rand int unsigned num_items;
  rand lower_env_item item[];  // array of lower items

  constraint item_cst { num_items == item.size();
                        num_items inside {[1:4]}; }
  constraint item_size_cst { max_item_size inside {[10:20]};}

  `uvm_object_utils_begin(upper_env_item)
    `uvm_field_int(max_item_size, UVM_DEFAULT)
    `uvm_field_int(num_items, UVM_DEFAULT)
    `uvm_field_array_object(item, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(input string name="upper_env_item");
    super.new(name);
  endfunction : new

  function void post_randomize();
    //item = new[num_items];
    foreach(item[i]) begin
     item[i] = lower_env_item::type_id::create($sformatf("item[%0d]", i));
     if (!item[i].randomize() with {pl_size <= max_item_size; })
       `uvm_error("RANDFAIL", "Item Randomization Failed") 
    end
  endfunction : post_randomize

endclass : upper_env_item

class upper_env_item_seq extends uvm_sequence #(lower_env_item);

  `uvm_object_utils(upper_env_item_seq)

  function new(string name="upper_env_item_seq");
    super.new(name);
  endfunction : new

  // This item contains an array of lower_env_items
  upper_env_item upper_item;

  virtual task pre_body();
     if (starting_phase !=null)
      starting_phase.raise_objection(this, "Running sequence");
  endtask

  virtual task post_body();
     if (starting_phase !=null)
      starting_phase.drop_objection(this, "Completed sequence");
  endtask

  virtual task body();
    // Create an upper-level item
    `uvm_create(upper_item)
    void'(upper_item.randomize());
    `uvm_info("UPPER_SEQ",
       {"Executing Upper Item:\n%s", upper_item.sprint()}, UVM_LOW)
    for (int i=0; i<upper_item.num_items; i++) 
      `uvm_send(upper_item.item[i])
  endtask : body
endclass : upper_env_item_seq

typedef class lower_env_sequencer;
class lower_env_base_seq extends uvm_sequence #(lower_env_item);
  `uvm_object_utils(lower_env_base_seq)
  `uvm_declare_p_sequencer(lower_env_sequencer)
   function new(string name="lower_env_base_seq");
     super.new(name);
   endfunction : new
   virtual task body();
     `uvm_info("LOWER_SEQ", "Executing...", UVM_LOW)
     `uvm_do(req)
   endtask : body
endclass : lower_env_base_seq


class lower_env_sequencer extends uvm_sequencer#(lower_env_item);
  `uvm_component_utils(lower_env_sequencer)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
endclass : lower_env_sequencer

class lower_env_driver extends uvm_driver#(lower_env_item);

  `uvm_component_utils(lower_env_driver)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  task run();
    get_and_drive();
  endtask : run

  task get_and_drive();
    while (1) begin
      seq_item_port.get_next_item(req);
      send_to_dut(req);
      seq_item_port.item_done();
    end
  endtask

  task send_to_dut(lower_env_item item);
    #10 `uvm_info("LOWER_DRIVER", {"Executing Lower Item:\n%s", item.sprint()}, UVM_LOW)
  endtask : send_to_dut

endclass : lower_env_driver

class simple_test extends uvm_test;

lower_env_driver driver;
lower_env_sequencer sequencer;

`uvm_component_utils(simple_test)
  function new(string name="simple_test", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "sequencer.run_phase", "default_sequence", upper_env_item_seq::get_type());
    sequencer = lower_env_sequencer::type_id::create("sequencer", this);
    driver    = lower_env_driver::type_id::create("driver", this);
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
  `uvm_info("TOP", "Beginning Test", UVM_LOW)
   run_test("simple_test");
end

endmodule : test
