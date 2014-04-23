// This file is generated using Cadence iregGen version 13.10.b030 

`ifndef RDB_SV
`define RDB_SV

// Input File: ex9-3_ua_simple_regs.xml

// Number of AddrMaps = 1
// Number of RegFiles = 1
// Number of Registers = 1
// Number of Memories = 0


//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 34


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

class uart_ctrl_rf_c extends uvm_reg_block;

  rand ua_lcr_c ua_lcr;

  virtual function void build();

    // Now create all registers

    ua_lcr = ua_lcr_c::type_id::create("ua_lcr", , get_full_name());

    // Now build the registers. Set parent and hdl_paths

    ua_lcr.configure(this, null, "ua_lcr_reg");
    ua_lcr.build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 1, UVM_LITTLE_ENDIAN);
    default_map.add_reg(ua_lcr, `UVM_REG_ADDR_WIDTH'h3, "RW");
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

`endif // RDB_SV
