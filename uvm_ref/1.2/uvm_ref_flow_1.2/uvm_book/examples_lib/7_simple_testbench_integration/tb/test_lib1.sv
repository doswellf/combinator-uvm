/*-------------------------------------------------------------------------
File name   : test_lib.sv
Title       : Library of tests
Project     :
Created     :
Description : Library of tests for the UART CONTROLLER Environment
Notes       : Includes all the base test and all test files.
----------------------------------------------------------------------*/

//----------------------------------------------------
// TEST:  uart_ctrl_base_test  (NO Stimulus)
//----------------------------------------------------
class uart_ctrl_base_test extends uvm_test;
uart_ctrl_tb uart_ctrl_tb0;

`uvm_component_utils(uart_ctrl_base_test)

virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  uart_ctrl_tb0 = uart_ctrl_tb::type_id::create("uart_ctrl_tb0", this);
endfunction : build_phase

task run_phase(uvm_phase phase);
  super.run_phase(phase);
  this.print();
endtask : run_phase

function new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

endclass : uart_ctrl_base_test

//----------------------------------------------------
// TEST:  u2a_a2u_rand_test  (NO VSEQ, NO DUT)
//----------------------------------------------------
class u2a_a2u_rand_test extends uart_ctrl_base_test;
  
`uvm_component_utils(u2a_a2u_rand_test)

virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  uvm_config_wrapper::set(this, "uart_ctrl_tb0.apb0.master.sequencer.run_phase",
            "default_sequence", apb_write_to_uart_seq::type_id::get());
  uvm_config_wrapper::set(this, "uart_ctrl_tb0.uart0.Tx.sequencer.run_phase",
            "default_sequence", uart_write_to_apb_seq::type_id::get());
endfunction : build_phase

function new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

endclass : u2a_a2u_rand_test

//----------------------------------------------------
// TEST:  u2a_a2u_vseq_test  (NO DUT)
//        Executes virtual sequence:  a2u_u2a_vseq 
//----------------------------------------------------
class u2a_a2u_vseq_test extends uart_ctrl_base_test;
  
  `uvm_component_utils(u2a_a2u_vseq_test)

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uvm_config_wrapper::set(this, "uart_ctrl_tb0.virtual_sequencer.run_phase",
            "default_sequence", a2u_u2a_vseq::type_id::get());
  endfunction : build_phase

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
endclass : u2a_a2u_vseq_test

//----------------------------------------------------
// SEQUENCE:  apb_config_seq 
//----------------------------------------------------
//class apb_config_seq extends uvm_sequence #(apb_transfer);
class apb_config_seq extends apb_master_base_seq;

  `uvm_object_utils(apb_config_seq)
  //`uvm_declare_p_sequencer(apb_master_sequencer)  // handled in base seq
  
  function new(string name="apb_config_seq");
    super.new(name);
  endfunction : new

  task body();
    `uvm_info("APB_CONFIG_SEQ", "Configuring the UART Controller...", UVM_LOW)
    // Actual details of the sequence go here...
    // This example is not connected to the DUT so just
    // generating messages 
    #10 `uvm_info("APB_CONFIG_SEQ", "Set Line Control Reg to 8'h83", UVM_MEDIUM)
    #10 `uvm_info("APB_CONFIG_SEQ", "Set Div Latch 1 to 8'h01", UVM_MEDIUM)
    #10 `uvm_info("APB_CONFIG_SEQ", "Set Div Latch 2 to 8'h00", UVM_MEDIUM)
    #10 `uvm_info("APB_CONFIG_SEQ", "Set Line Control Reg to 8'h03", UVM_MEDIUM)
    #10 `uvm_info("APB_CONFIG_SEQ", "Configuring the UART Controller Completed...", UVM_LOW)
  endtask : body
endclass : apb_config_seq

//----------------------------------------------------
// SEQUENCE:  apb_write_to_uart_seq 
//----------------------------------------------------
class apb_write_to_uart_seq extends apb_master_base_seq;

 rand int num_transfers;
 constraint num_transfers_c {num_transfers inside {[2:8]};}

  `uvm_object_utils(apb_write_to_uart_seq)
  //`uvm_declare_p_sequencer(apb_master_sequencer)  // handled in base seq
  
  function new(string name="apb_write_to_uart_seq");
    super.new(name);
  endfunction : new

  task body();
    apb_transfer transfer;
    `uvm_info("APB_TO_UART_SEQ", "Executing...", UVM_LOW)
    // Actual details of the sequence go here...
    // This example is not connected to the DUT so just
    // generating a few transactions to print
    transfer = apb_transfer::type_id::create("transfer");
    repeat (num_transfers) begin
       void'(transfer.randomize()); 
       #10 `uvm_info("APB_TO_UART_SEQ",
            {"Sending Transfer to Driver...\n", transfer.sprint()}, UVM_MEDIUM)
    end
  # 10  `uvm_info("APB_TO_UART_SEQ", "Completed...", UVM_LOW)
  endtask : body
endclass : apb_write_to_uart_seq

//----------------------------------------------------
// SEQUENCE:  uart_write_to_apb_seq 
//----------------------------------------------------
//class uart_write_to_apb_seq extends uvm_sequence #(uart_frame);
class uart_write_to_apb_seq extends uart_base_seq;

 rand int num_frames;
 constraint num_frames_c {num_frames inside {[1:5]};}

`uvm_object_utils(uart_write_to_apb_seq)
//`uvm_declare_p_sequencer(uart_sequencer) // handled in base seq

function new(string name="uart_write_to_apb_seq");
  super.new(name);
endfunction : new

task body();
  uart_frame frame;
  `uvm_info("UART_TO_APB_SEQ", "Executing...", UVM_LOW)
  // Actual details of the sequence go here...
  // This example is not connected to the DUT so just
  // generating a few transactions to print
  frame = uart_frame::type_id::create("frame");
  repeat (num_frames) begin
     void'(frame.randomize()); 
     #20 `uvm_info("UART_TO_APB_SEQ",
            {"Sending Frame to Driver...\n", frame.sprint()}, UVM_MEDIUM)
    end
  # 10  `uvm_info("UART_TO_APB_SEQ", "Completed...", UVM_LOW)
endtask : body

endclass : uart_write_to_apb_seq

//----------------------------------------------------
// SEQUENCE:  base_vseq - Base for Virtual Sequences
//----------------------------------------------------
class base_vseq extends uvm_sequence;

  function new(string name="base_vseq");
      super.new(name);
  endfunction : new

 `uvm_object_utils(base_vseq)
 `uvm_declare_p_sequencer(uart_ctrl_virtual_sequencer)

  virtual task pre_body();
     if (starting_phase != null)
        starting_phase.raise_objection(this, "Running sequence");
  endtask : pre_body

  virtual task post_body();
     if (starting_phase != null)
        starting_phase.drop_objection(this, "Completed sequence");
  endtask
endclass : base_vseq

//---------------------------------------------------------------
// SEQUENCE:  a2u_u2a_vseq  - Virtual Sequence Example (NO DUT)
//---------------------------------------------------------------
class a2u_u2a_vseq extends base_vseq;

  `uvm_object_utils(a2u_u2a_vseq)
  `uvm_declare_p_sequencer(uart_ctrl_virtual_sequencer)

  function new(string name="a2u_u2a_vseq");
    super.new(name);
  endfunction : new

  // APB Sequences
  apb_config_seq  config_seq;       // Configures UART Controller
  apb_write_to_uart_seq  a2u_seq; 

  // UART Sequences
  uart_write_to_apb_seq  u2a_seq;  

  task body();
    `uvm_info("A2U_U2A_VSEQ", "Executing...", UVM_LOW)
    `uvm_do_on(config_seq, p_sequencer.apb_seqr)
    // Then execute the u2a and a2u sequences in parallel
    fork
      `uvm_do_on(u2a_seq, p_sequencer.uart_seqr)
      `uvm_do_on(a2u_seq, p_sequencer.apb_seqr)
    join
  endtask : body
endclass : a2u_u2a_vseq
