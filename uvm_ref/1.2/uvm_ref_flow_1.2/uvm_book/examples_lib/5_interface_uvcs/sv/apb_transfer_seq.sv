/*******************************************************************************
  APB Transfer Sequence
*******************************************************************************/
//------------------------------------------------------------------------------
// SEQUENCE: apb_transfer_seq
//------------------------------------------------------------------------------
class apb_transfer_seq extends uvm_sequence #(apb_transfer);

  function new(string name="apb_transfer_seq");
    super.new(name);
  endfunction
 
  `uvm_object_utils(apb_transfer_seq)

  // A simple sequence to execute a single random APB transfer
  virtual task body();
     // Raise end-of phase objection
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence:",
                                              get_full_name()});

    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    // Execute an APB transfer
    `uvm_do(req)

    // NOTE:  The above macro expands to the following:
    //    req = apb_transfer::type_id::create("req");
    //    start_item(req);
    //    if(!req.randomize())
    //      `uvm_warning("RNDFLD", "Randomization failed")
    //    finish_item(req);

     // Drop end-of-phase objection
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence:",
                                             get_full_name()});
  endtask
endclass : apb_transfer_seq

