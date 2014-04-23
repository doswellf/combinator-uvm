//------------------------------------------------------------------------------
// SEQUENCE: apb_traffic_seq
//------------------------------------------------------------------------------
class apb_traffic_seq extends uvm_sequence #(apb_transfer);

  multi_apb_transfer_seq   multi_seq;   // rand param: num_seq
  apb_write_read_word_seq  wr_rd_seq;   // rand param: start_addr

  // Constructor and UVM automation macros
  `uvm_object_utils(apb_traffic_seq)

  function new(string name="apb_traffic_seq");
    super.new(name);
  endfunction

  // The body executes two pre-defined sequences with constraints
  virtual task body();
     // Raise end-of phase objection
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence:",
                                              get_full_name()});

    `uvm_info(get_type_name(), "Starting...", UVM_HIGH)
    repeat (5)
      `uvm_do_with( wr_rd_seq, { start_addr inside {['h0000:'h1fff]}; } )
    `uvm_do_with( multi_seq, { num_seq == 5; } )
    repeat (5)
     `uvm_do_with(wr_rd_seq, { start_addr inside {['h2000:'hffff]};})

     // Drop end-of-phase objection
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence:",
                                              get_full_name()});
  endtask : body
endclass : apb_traffic_seq
