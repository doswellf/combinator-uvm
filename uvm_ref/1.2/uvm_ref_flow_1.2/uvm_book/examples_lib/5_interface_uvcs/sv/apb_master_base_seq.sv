//------------------------------------------------------------------------------
// SEQUENCE: apb_master_base_seq
//------------------------------------------------------------------------------
class apb_master_base_seq extends uvm_sequence #(apb_transfer);

  // Constructor and UVM automation macros
  function new(string name="apb_master_base_seq");
    super.new(name);
  endfunction

  `uvm_object_utils(apb_master_base_seq)
  `uvm_declare_p_sequencer(apb_master_sequencer)

  virtual task pre_body();
    // Raise end-of phase objection if started as a root sequence
    if (starting_phase != null)
      starting_phase.raise_objection(this, { "Running sequence '",
                                     get_full_name(), "'"});
  endtask

  virtual task post_body();
     // Drop end-of-phase objection if started as a root sequence
     if (starting_phase != null)
      starting_phase.drop_objection(this, { "Completed sequence '",
                                     get_full_name(), "'"});
  endtask
endclass : apb_master_base_seq
