/**************************************************************************
  Example 9-13: Divisor Latch Byte 0 with auto-generated coverage

  This example does not run stand-alone
**************************************************************************/
class ua_div_latch0_c extends uvm_reg;

  rand uvm_reg_field div_val;

  constraint c_div_val { div_val.value == 1; }
  virtual function void build();
    div_val = uvm_reg_field::type_id::create("div_val");
    div_val.configure(this, 8, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h00>>0, 1, 1, 1);
    wr_cg.set_inst_name($sformatf("%s.wcov", get_full_name()));
    rd_cg.set_inst_name($sformatf("%s.rcov", get_full_name()));
  endfunction

  covergroup wr_cg;
    option.per_instance=1;
    div_val : coverpoint div_val.value[7:0];
  endgroup
  covergroup rd_cg;
    option.per_instance=1;
    div_val : coverpoint div_val.value[7:0];
  endgroup

  protected virtual function void sample(uvm_reg_data_t  data, byte_en, bit is_read, uvm_reg_map map);
    super.sample(data, byte_en, is_read, map);
    if(!is_read) wr_cg.sample();
    if(is_read) rd_cg.sample();
  endfunction

  `uvm_register_cb(ua_div_latch0_c, uvm_reg_cbs) 
  `uvm_set_super_type(ua_div_latch0_c, uvm_reg)
  `uvm_object_utils(ua_div_latch0_c)
  function new(input string name="unnamed-ua_div_latch0_c");
    super.new(name, 8, build_coverage(UVM_CVR_FIELD_VALS));
    wr_cg=new;
    rd_cg=new;
  endfunction : new
endclass : ua_div_latch0_c
