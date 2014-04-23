/*******************************************************************************
  FILE : ex5-20_uvm_sequence_library.sv
*******************************************************************************/
//------------------------------------------------------------------------------
// SEQUENCE LIBRARY: mydut_seq_lib
//------------------------------------------------------------------------------
class mydut_seq_lib extends uvm_sequence_library #(apb_transfer);

  `uvm_object_utils(mydut_seq_lib)
  `uvm_sequence_library_utils(mydut_seq_lib)

  function new(string name="apb_master_base_seq");
    super.new(name);
    // built-in fields
    min_random_count = 1;
    max_random_count = 5;
    // add sequences for this library
    add_typewide_sequence(apb_transfer_seq::get_type());
    add_typewide_sequence(multi_apb_transfer_seq::get_type());
    add_typewide_sequence(apb_write_read_seq::get_type());
    add_typewide_sequence(apb_traffic_seq::get_type());
    init_sequence_library();
  endfunction
 
endclass : mydut_seq_lib
