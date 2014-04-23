// This file is generated using Cadence iregGen version 13.10.b030 

`ifndef UART_CTRL_REGS_SV
`define UART_CTRL_REGS_SV

// Input File: uart_ctrl_regs.xml

// Number of AddrMaps = 1
// Number of RegFiles = 1
// Number of Registers = 6
// Number of Memories = 0


//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 263


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

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 288


class ua_div_latch1_c extends uvm_reg;

  rand uvm_reg_field div_val;

  constraint c_div_val { div_val.value == 0; }
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

  `uvm_register_cb(ua_div_latch1_c, uvm_reg_cbs) 
  `uvm_set_super_type(ua_div_latch1_c, uvm_reg)
  `uvm_object_utils(ua_div_latch1_c)
  function new(input string name="unnamed-ua_div_latch1_c");
    super.new(name, 8, build_coverage(UVM_CVR_FIELD_VALS));
    wr_cg=new;
    rd_cg=new;
  endfunction : new
endclass : ua_div_latch1_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 83


class ua_int_id_c extends uvm_reg;

  uvm_reg_field priority_bit;
  uvm_reg_field bit1;
  uvm_reg_field bit2;
  uvm_reg_field bit3;

  virtual function void build();
    priority_bit = uvm_reg_field::type_id::create("priority_bit");
    priority_bit.configure(this, 1, 0, "RO", 0, `UVM_REG_DATA_WIDTH'hC1>>0, 1, 0, 1);
    bit1 = uvm_reg_field::type_id::create("bit1");
    bit1.configure(this, 1, 1, "RO", 0, `UVM_REG_DATA_WIDTH'hC1>>1, 1, 0, 1);
    bit2 = uvm_reg_field::type_id::create("bit2");
    bit2.configure(this, 1, 2, "RO", 0, `UVM_REG_DATA_WIDTH'hC1>>2, 1, 0, 1);
    bit3 = uvm_reg_field::type_id::create("bit3");
    bit3.configure(this, 1, 3, "RO", 0, `UVM_REG_DATA_WIDTH'hC1>>3, 1, 0, 1);
    rd_cg.set_inst_name($sformatf("%s.rcov", get_full_name()));
  endfunction

  covergroup rd_cg;
    option.per_instance=1;
    priority_bit : coverpoint priority_bit.value[0:0];
    bit1 : coverpoint bit1.value[0:0];
    bit2 : coverpoint bit2.value[0:0];
    bit3 : coverpoint bit3.value[0:0];
  endgroup

  protected virtual function void sample(uvm_reg_data_t  data, byte_en, bit is_read, uvm_reg_map map);
    super.sample(data, byte_en, is_read, map);
    if(is_read) rd_cg.sample();
  endfunction

  `uvm_register_cb(ua_int_id_c, uvm_reg_cbs) 
  `uvm_set_super_type(ua_int_id_c, uvm_reg)
  `uvm_object_utils(ua_int_id_c)
  function new(input string name="unnamed-ua_int_id_c");
    super.new(name, 8, build_coverage(UVM_CVR_FIELD_VALS));
    rd_cg=new;
  endfunction : new
endclass : ua_int_id_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 140


class ua_fifo_ctrl_c extends uvm_reg;

  rand uvm_reg_field rx_clear;
  rand uvm_reg_field tx_clear;
  rand uvm_reg_field rx_fifo_int_trig_level;

  virtual function void build();
    rx_clear = uvm_reg_field::type_id::create("rx_clear");
    rx_clear.configure(this, 1, 1, "WO", 0, `UVM_REG_DATA_WIDTH'hC0>>1, 1, 1, 1);
    tx_clear = uvm_reg_field::type_id::create("tx_clear");
    tx_clear.configure(this, 1, 2, "WO", 0, `UVM_REG_DATA_WIDTH'hC0>>2, 1, 1, 1);
    rx_fifo_int_trig_level = uvm_reg_field::type_id::create("rx_fifo_int_trig_level");
    rx_fifo_int_trig_level.configure(this, 2, 6, "WO", 0, `UVM_REG_DATA_WIDTH'hC0>>6, 1, 1, 1);
    wr_cg.set_inst_name($sformatf("%s.wcov", get_full_name()));
  endfunction

  covergroup wr_cg;
    option.per_instance=1;
    rx_clear : coverpoint rx_clear.value[0:0];
    tx_clear : coverpoint tx_clear.value[0:0];
    rx_fifo_int_trig_level : coverpoint rx_fifo_int_trig_level.value[1:0];
  endgroup

  protected virtual function void sample(uvm_reg_data_t  data, byte_en, bit is_read, uvm_reg_map map);
    super.sample(data, byte_en, is_read, map);
    if(!is_read) wr_cg.sample();
  endfunction

  `uvm_register_cb(ua_fifo_ctrl_c, uvm_reg_cbs) 
  `uvm_set_super_type(ua_fifo_ctrl_c, uvm_reg)
  `uvm_object_utils(ua_fifo_ctrl_c)
  function new(input string name="unnamed-ua_fifo_ctrl_c");
    super.new(name, 8, build_coverage(UVM_CVR_FIELD_VALS));
    wr_cg=new;
  endfunction : new
endclass : ua_fifo_ctrl_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 189


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
    wr_cg.set_inst_name($sformatf("%s.wcov", get_full_name()));
    rd_cg.set_inst_name($sformatf("%s.rcov", get_full_name()));
  endfunction

  covergroup wr_cg;
    option.per_instance=1;
    char_lngth : coverpoint char_lngth.value[1:0];
    num_stop_bits : coverpoint num_stop_bits.value[0:0];
    p_en : coverpoint p_en.value[0:0];
    parity_even : coverpoint parity_even.value[0:0];
    parity_sticky : coverpoint parity_sticky.value[0:0];
    break_ctrl : coverpoint break_ctrl.value[0:0];
    div_latch_access : coverpoint div_latch_access.value[0:0];
  endgroup
  covergroup rd_cg;
    option.per_instance=1;
    char_lngth : coverpoint char_lngth.value[1:0];
    num_stop_bits : coverpoint num_stop_bits.value[0:0];
    p_en : coverpoint p_en.value[0:0];
    parity_even : coverpoint parity_even.value[0:0];
    parity_sticky : coverpoint parity_sticky.value[0:0];
    break_ctrl : coverpoint break_ctrl.value[0:0];
    div_latch_access : coverpoint div_latch_access.value[0:0];
  endgroup

  protected virtual function void sample(uvm_reg_data_t  data, byte_en, bit is_read, uvm_reg_map map);
    super.sample(data, byte_en, is_read, map);
    if(!is_read) wr_cg.sample();
    if(is_read) rd_cg.sample();
  endfunction

  `uvm_register_cb(ua_lcr_c, uvm_reg_cbs) 
  `uvm_set_super_type(ua_lcr_c, uvm_reg)
  `uvm_object_utils(ua_lcr_c)
  function new(input string name="unnamed-ua_lcr_c");
    super.new(name, 8, build_coverage(UVM_CVR_FIELD_VALS));
    wr_cg=new;
    rd_cg=new;
  endfunction : new
endclass : ua_lcr_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 26


class ua_ier_c extends uvm_reg;

  rand uvm_reg_field rx_data;
  rand uvm_reg_field tx_data;
  rand uvm_reg_field rx_line_sts;
  rand uvm_reg_field mdm_sts;

  virtual function void build();
    rx_data = uvm_reg_field::type_id::create("rx_data");
    rx_data.configure(this, 1, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h00>>0, 1, 1, 1);
    tx_data = uvm_reg_field::type_id::create("tx_data");
    tx_data.configure(this, 1, 1, "RW", 0, `UVM_REG_DATA_WIDTH'h00>>1, 1, 1, 1);
    rx_line_sts = uvm_reg_field::type_id::create("rx_line_sts");
    rx_line_sts.configure(this, 1, 2, "RW", 0, `UVM_REG_DATA_WIDTH'h00>>2, 1, 1, 1);
    mdm_sts = uvm_reg_field::type_id::create("mdm_sts");
    mdm_sts.configure(this, 1, 3, "RW", 0, `UVM_REG_DATA_WIDTH'h00>>3, 1, 1, 1);
    wr_cg.set_inst_name($sformatf("%s.wcov", get_full_name()));
    rd_cg.set_inst_name($sformatf("%s.rcov", get_full_name()));
  endfunction

  covergroup wr_cg;
    option.per_instance=1;
    rx_data : coverpoint rx_data.value[0:0];
    tx_data : coverpoint tx_data.value[0:0];
    rx_line_sts : coverpoint rx_line_sts.value[0:0];
    mdm_sts : coverpoint mdm_sts.value[0:0];
  endgroup
  covergroup rd_cg;
    option.per_instance=1;
    rx_data : coverpoint rx_data.value[0:0];
    tx_data : coverpoint tx_data.value[0:0];
    rx_line_sts : coverpoint rx_line_sts.value[0:0];
    mdm_sts : coverpoint mdm_sts.value[0:0];
  endgroup

  protected virtual function void sample(uvm_reg_data_t  data, byte_en, bit is_read, uvm_reg_map map);
    super.sample(data, byte_en, is_read, map);
    if(!is_read) wr_cg.sample();
    if(is_read) rd_cg.sample();
  endfunction

  `uvm_register_cb(ua_ier_c, uvm_reg_cbs) 
  `uvm_set_super_type(ua_ier_c, uvm_reg)
  `uvm_object_utils(ua_ier_c)
  function new(input string name="unnamed-ua_ier_c");
    super.new(name, 8, build_coverage(UVM_CVR_FIELD_VALS));
    wr_cg=new;
    rd_cg=new;
  endfunction : new
endclass : ua_ier_c

class uart_ctrl_rf_c extends uvm_reg_block;

  rand ua_div_latch0_c ua_div_latch0;
  rand ua_div_latch1_c ua_div_latch1;
  rand ua_int_id_c ua_int_id;
  rand ua_fifo_ctrl_c ua_fifo_ctrl;
  rand ua_lcr_c ua_lcr;
  rand ua_ier_c ua_ier;

  virtual function void build();

    // Now create all registers

    ua_div_latch0 = ua_div_latch0_c::type_id::create("ua_div_latch0", , get_full_name());
    ua_div_latch1 = ua_div_latch1_c::type_id::create("ua_div_latch1", , get_full_name());
    ua_int_id = ua_int_id_c::type_id::create("ua_int_id", , get_full_name());
    ua_fifo_ctrl = ua_fifo_ctrl_c::type_id::create("ua_fifo_ctrl", , get_full_name());
    ua_lcr = ua_lcr_c::type_id::create("ua_lcr", , get_full_name());
    ua_ier = ua_ier_c::type_id::create("ua_ier", , get_full_name());

    // Now build the registers. Set parent and hdl_paths

    ua_div_latch0.configure(this, null, "ua_div_latch0_reg");
    ua_div_latch0.build();
    ua_div_latch1.configure(this, null, "ua_div_latch1_reg");
    ua_div_latch1.build();
    ua_int_id.configure(this, null, "ua_int_id_reg");
    ua_int_id.build();
    ua_fifo_ctrl.configure(this, null, "ua_fifo_ctrl_reg");
    ua_fifo_ctrl.build();
    ua_lcr.configure(this, null, "ua_lcr_reg");
    ua_lcr.build();
    ua_ier.configure(this, null, "ua_ier_reg");
    ua_ier.build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 1, UVM_LITTLE_ENDIAN);
    default_map.add_reg(ua_div_latch0, `UVM_REG_ADDR_WIDTH'h0, "RW");
    default_map.add_reg(ua_div_latch1, `UVM_REG_ADDR_WIDTH'h1, "RW");
    default_map.add_reg(ua_int_id, `UVM_REG_ADDR_WIDTH'h2, "RO");
    default_map.add_reg(ua_fifo_ctrl, `UVM_REG_ADDR_WIDTH'h2, "WO");
    default_map.add_reg(ua_lcr, `UVM_REG_ADDR_WIDTH'h3, "RW");
    default_map.add_reg(ua_ier, `UVM_REG_ADDR_WIDTH'h8, "RW");
  endfunction

  `uvm_object_utils(uart_ctrl_rf_c)
  function new(input string name="unnamed-uart_ctrl_rf");
    super.new(name, UVM_NO_COVERAGE);
  endfunction : new

endclass : uart_ctrl_rf_c

//////////////////////////////////////////////////////////////////////////////
// Address_map definition
//////////////////////////////////////////////////////////////////////////////
class uart_ctrl_addr_map_c extends uvm_reg_block;

  rand uart_ctrl_rf_c uart_ctrl_rf;

  function void build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 1, UVM_LITTLE_ENDIAN);
    uart_ctrl_rf = uart_ctrl_rf_c::type_id::create("uart_ctrl_rf", , get_full_name());
    uart_ctrl_rf.configure(this, "rf1");
    uart_ctrl_rf.build();
    uart_ctrl_rf.lock_model();
    default_map.add_submap(uart_ctrl_rf.default_map, `UVM_REG_ADDR_WIDTH'h0);
    set_hdl_path_root("addr_map");
    this.lock_model();
    default_map.set_check_on_read();
  endfunction
  `uvm_object_utils(uart_ctrl_addr_map_c)
  function new(input string name="unnamed-uart_ctrl_addr_map_c");
    super.new(name, UVM_NO_COVERAGE);
  endfunction
endclass : uart_ctrl_addr_map_c

`endif // UART_CTRL_REGS_SV
