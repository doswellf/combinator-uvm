/**************************************************************************
  Example 9-12: Multi-register Sequence Example

  This example does not run stand-alone
**************************************************************************/

class multi_reg_seq extends base_reg_seq;

  uvm_reg_mem_built_in_seq seq;

  `uvm_object_utils(multi_reg_seq)
  function new(string name="multi_reg_seq");
    super.new(name);
  endfunction

  virtual task body();
    uvm_status_e status;
    uvm_reg regs[$];   // queue of registers
    bit [63:0] rval;

    `uvm_info("REG_SEQ", "Executing Sequence", UVM_HIGH)
    void'(model.randomize());    // RANDOMIZE the whole model
    model.get_registers(regs);
    // Now UPDATE each Register
    foreach(regs[i]) begin
      regs[i].update(rstatus, UVM_FRONTDOOR);
      `uvm_info("REG_SEQ", $sformatf("%s UPDATE:0x%h",
                regs[i].get_name(), regs[i].get()), UVM_LOW)
    end
    // Now READ each Register
    foreach(regs[i]) begin
      regs[i].read(rstatus, rval);
      `uvm_info("REG_SEQ", $sformatf("%s   READ:0x%h",
                regs[i].get_name(), rval), UVM_LOW)
    end
    `uvm_info("REG_SEQ", "Sequence Completed", UVM_HIGH)
  endtask

endclass : multi_reg_seq
