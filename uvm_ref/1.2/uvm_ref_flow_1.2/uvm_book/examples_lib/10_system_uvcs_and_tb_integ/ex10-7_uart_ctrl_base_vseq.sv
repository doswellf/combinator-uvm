/**********************************************************************
  Example 10-7: UART Controller Base Virtual Sequence

  %  irun -uvm ex10-7 uart_ctrl_base_vseq.sv
 
  This code came from:
  Kit Location : $UVM_REF_HOME/soc_verification_libs/sv_cb_ex_lib/uart_ctrl/sv/sequence_lib/uart_ctrl_virtual-seq_lib.sv
*********************************************************************/

class base_vseq extends uvm_sequence;
  function new(string name="base_vseq");
    super.new(name);
  endfunction

  `uvm_object_utils(base_vseq)
 `uvm_declare_p_sequencer(uart_ctrl_virtual_sequencer)

// Use a base sequence to raise/drop objections if this is a default sequence
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
endclass : base_vseq
