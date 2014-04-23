/****************************************************************
  Example 7-14: UART Controller Virtual Sequence (Base Sequence)

  No testcase for this example.  Please run the full example
****************************************************************/

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
