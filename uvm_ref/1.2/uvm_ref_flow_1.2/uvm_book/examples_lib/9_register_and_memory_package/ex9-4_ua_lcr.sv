// Example 9-4:  UART Controller Line Control Register SystemVerilog Code
//------------------------------------------------
// This is an incomplete example showing just the register definition results
// Generated from Input File: ex9-3_ua_simple_regs.xml
//------------------------------------------------
// Generated rdb.sv by executing:
//   %  runreg -i ex9-3_ua_simple_regs.xml -nc -uvm11a
//////////////////////////////////////////////////////////////////////
// Register definition 
////////////////////////////////////////////////////////////////////// 
class ua_lcr_c extends uvm_reg;

  rand uvm_reg_field char_lngth;
  rand uvm_reg_field num_stop_bits;
  rand uvm_reg_field p_en;
  rand uvm_reg_field parity_even;
  rand uvm_reg_field parity_sticky;
  rand uvm_reg_field break_ctrl;
  rand uvm_reg_field div_latch_access;

  constraint c_char_lngth { char_lngth.value != 2'b00; }
  constraint c_break_ctrl { break_ctrl.value == 1'b0; }
  virtual function void build();
    char_lngth = uvm_reg_field::type_id::create("char_lngth");
    char_lngth.configure(this, 2, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>0, 1, 1, 1);
    num_stop_bits = uvm_reg_field::type_id::create("num_stop_bits");
    num_stop_bits.configure(this, 1, 2, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>2, 1, 1, 1);
    p_en = uvm_reg_field::type_id::create("p_en");
    p_en.configure(this, 1, 3, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>3, 1, 1, 1);
    parity_even = uvm_reg_field::type_id::create("parity_even");
    parity_even.configure(this, 1, 4, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>4, 1, 1, 1);
    parity_sticky = uvm_reg_field::type_id::create("parity_sticky");
    parity_sticky.configure(this, 1, 5, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>5, 1, 1, 1);
    break_ctrl = uvm_reg_field::type_id::create("break_ctrl");
    break_ctrl.configure(this, 1, 6, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>6, 1, 1, 1);
    div_latch_access = uvm_reg_field::type_id::create("div_latch_access");
    div_latch_access.configure(this, 1, 7, "RW", 0, `UVM_REG_DATA_WIDTH'h03>>7, 1, 1, 1);
  endfunction

  `uvm_register_cb(ua_lcr_c, uvm_reg_cbs)
  `uvm_set_super_type(ua_lcr_c, uvm_reg)
  `uvm_object_utils(ua_lcr_c)
  function new(input string name="unnamed-ua_lcr_c");
    super.new(name, 8, UVM_NO_COVERAGE);
  endfunction : new
endclass : ua_lcr_c
