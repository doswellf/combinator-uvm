//------------------------------------------------------------------------------
// SEQUENCE: multi_apb_transfer_seq
//------------------------------------------------------------------------------
class multi_apb_transfer_seq extends uvm_sequence #(apb_transfer);

  rand int num_seq;
  constraint c_num_seq { num_seq inside {[1:10]}; }

  // Constructor and UVM automation macros
  `uvm_object_utils(multi_apb_transfer_seq)
  function new(string name="multi_apb_transfer_seq");
    super.new(name);
  endfunction

  virtual task body();
     apb_transfer_seq apb_seq;  // Instance of another sequence type
     // Raise end-of phase objection
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence:",
                                              get_full_name()});

    // Execute multiple APB transfers
    repeat(num_seq)
      `uvm_do(apb_seq)

     // Drop end-of-phase objection
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence:",
                                              get_full_name()});
  endtask
endclass : multi_apb_transfer_seq
