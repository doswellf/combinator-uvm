//------------------------------------------------------------------------------
// SEQUENCE: apb_write_read_word_seq
//------------------------------------------------------------------------------
class apb_write_read_word_seq extends uvm_sequence #(apb_transfer);

  rand bit [31:0] start_addr;
  // Constrain the lsb's to 'b00 for word-aligned transfer
  constraint c_start_addr { start_addr[1:0] == 2'b00; }

  // Constructor and UVM automation macros
  `uvm_object_utils(apb_write_read_word_seq)

  function new(string name="apb_write_read_word_seq");
    super.new(name);
  endfunction

  virtual task body();
    // Raise end-of phase objection
    if (starting_phase != null)
      starting_phase.raise_objection(this, {"Running sequence:",
                                            get_full_name()});

    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    // write one transfer
    `uvm_do_with(req, { req.addr == start_addr;
                        req.direction == APB_WRITE; })
    // read from the same address
    `uvm_do_with(req, { req.addr == start_addr;
                        req.direction == APB_READ; })
    // NOTE:  The `uvm_do_with macro expands to the following:
    //    req = apb_transfer::type_id::create("req");
    //    start_item(req);
    //    if(!req.randomize() with {req.addr == start_addr;
    //                              req.direction == APB_WRITE; })
    //      `uvm_warning("RNDFLD", "Randomization failed")
    //    finish_item(req);

    // Drop end-of-phase objection
    if (starting_phase != null)
       starting_phase.drop_objection(this, {"Completed sequence:",
                                             get_full_name()});
  endtask : body

endclass : apb_write_read_word_seq
