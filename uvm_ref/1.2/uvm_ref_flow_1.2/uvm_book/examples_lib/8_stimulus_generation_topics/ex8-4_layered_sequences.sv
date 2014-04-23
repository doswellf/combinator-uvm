/*----------------------------------------------------------------------
  Example 8-4: Connecting Layered Sequences

  %  irun -uvm ex8-4_layered_sequences.sv
----------------------------------------------------------------------*/
module test;
import uvm_pkg::*;
`include "uvm_macros.svh"

// Lower-Env Item - an array of bytes
class lower_item extends uvm_sequence_item;
  rand byte byte_array[];
  rand int unsigned num_bytes;
  constraint a_cst { num_bytes inside {[1:16]}; 
                     byte_array.size() == num_bytes; }

  `uvm_object_utils_begin(lower_item)
     `uvm_field_int(num_bytes, UVM_DEFAULT | UVM_DEC)
     `uvm_field_array_int(byte_array, UVM_DEFAULT)
  `uvm_object_utils_end
 
  function new (string name="lower_item");
    super.new(name);
  endfunction : new

endclass : lower_item

// Upper-Env Item - a header(byte), a word (4-bytes) and a footer (byte)
class upper_item extends uvm_sequence_item;
  rand byte header;
  rand bit [31:0] word;
  rand byte footer;

  `uvm_object_utils_begin(upper_item)
    `uvm_field_int(header, UVM_DEFAULT)
    `uvm_field_int(word, UVM_DEFAULT)
    `uvm_field_int(footer, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(input string name="upper_item");
    super.new(name);
  endfunction : new

endclass : upper_item

class upper_sequencer extends uvm_sequencer#(upper_item);
  `uvm_component_utils(upper_sequencer)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
endclass : upper_sequencer

class lower_sequencer extends uvm_sequencer#(lower_item);
  //NEW: TLM port for getting upper_env data items
  uvm_seq_item_pull_port #(upper_item) upper_seq_item_port;

  `uvm_component_utils(lower_sequencer)
  function new(string name, uvm_component parent);
    super.new(name, parent);
    upper_seq_item_port = new("upper_seq_item_port", this);
  endfunction : new
endclass : lower_sequencer

class lower_driver extends uvm_driver#(lower_item);
  `uvm_component_utils(lower_driver)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  task run_phase(uvm_phase phase);
    while (1) begin
      seq_item_port.get_next_item(req);
      send_to_dut(req);
      seq_item_port.item_done();
    end
  endtask: run_phase

  task send_to_dut(lower_item item);
   #10 `uvm_info("LOWER_DRIVER", {"Executing Lower Item:\n%s", item.sprint()}, UVM_LOW)
  endtask : send_to_dut
endclass : lower_driver

class upper_to_lower_seq extends uvm_sequence #(lower_item);
  `uvm_object_utils(upper_to_lower_seq)
  `uvm_declare_p_sequencer(lower_sequencer)
  function new(string name="upper_to_lower_seq");
    super.new(name);
  endfunction : new

  upper_item u_item;
  lower_item l_item;

  virtual task body();
    forever begin
      `uvm_info("UP2LOW_SEQ", "Executing...", UVM_LOW)
      `uvm_do_with(l_item,
                  { l_item.num_bytes == 6;
                    l_item.byte_array[0] == u_item.header;
                    l_item.byte_array[1] == u_item.word[7:0];
                    l_item.byte_array[2] == u_item.word[15:8];
                    l_item.byte_array[3] == u_item.word[23:16];
                    l_item.byte_array[4] == u_item.word[31:24];
                    l_item.byte_array[5] == u_item.footer;
                   })
    end
   endtask : body

  // In the pre_do task, pull an upper item from the upper sequencer.
  virtual task pre_do(bit is_item);
    if (is_item)
       p_sequencer.upper_seq_item_port.get_next_item(u_item);
        `uvm_info("UP2LOW_SEQ",
       {"Executing Upper Item:\n%s", u_item.sprint()}, UVM_LOW)
  endtask : pre_do

  // In the post_do task, signal the upper sequencer we are done. If desired,
  // update the upper-item properties for the upper sequencer to use.
  virtual function void post_do(uvm_sequence_item this_item);
    p_sequencer.upper_seq_item_port.item_done(u_item);
  endfunction : post_do
endclass : upper_to_lower_seq

class simple_env extends uvm_env;
  // Components of this environment: in a reusable env, the lower driver
  // and sequencer would be in an agent
  lower_driver l_driver;        
  lower_sequencer l_sequencer;
  upper_sequencer u_sequencer;

  `uvm_component_utils(simple_env)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    l_sequencer = lower_sequencer::type_id::create("l_sequencer", this);
    u_sequencer = upper_sequencer::type_id::create("u_sequencer", this);
    l_driver = lower_driver::type_id::create("l_driver", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    l_driver.seq_item_port.connect(l_sequencer.seq_item_export);
    l_driver.rsp_port.connect(l_sequencer.rsp_export);
    l_sequencer.upper_seq_item_port.connect(u_sequencer.seq_item_export);
  endfunction : connect_phase
endclass : simple_env

class simple_test extends uvm_test;

 simple_env env;

`uvm_component_utils(simple_test)
  function new(string name="simple_test", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uvm_config_wrapper::set(this, "l_sequencer.run_phase", "default_sequence", upper_to_lower_seq::get_type());
    env = simple_env::type_id::create("env", this);
  endfunction : build_phase

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
