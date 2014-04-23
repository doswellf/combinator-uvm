/**************************************************************************
  Example 9-11: Using UVM Built-in Sequences

  This example does not run stand-alone
**************************************************************************/

class built_in_seq extends base_reg_seq;

  uvm_reg_mem_built_in_seq seq;

  `uvm_object_utils(built_in_seq)
  function new(string name="built_in_seq");
    super.new(name);
  endfunction

  virtual task body();
    uvm_status_e status;
    `uvm_info("REG_SEQ", "Executing Sequence", UVM_HIGH)
    seq = uvm_reg_mem_built_in_seq::type_id::create("seq");
    seq.model = model;  // set the register model
    seq.tests = UVM_DO_ALL_REG_MEM_TESTS
             // &  ~(UVM_DO_REG_HW_RESET)
             // &  ~(UVM_DO_REG_BIT_BASH)
             // &  ~(UVM_DO_REG_ACCESS)
             // &  ~(UVM_DO_MEM_ACCESS)
             // &  ~(UVM_DO_SHARED_ACCESS)
             // &  ~(UVM_DO_MEM_WALK)
                ;
    seq.start(null); 
    `uvm_info("REG_SEQ", "Sequence Completed", UVM_HIGH)
  endtask

endclass : built_in_seq
