`ifndef SPI_RDB_SV
`define SPI_RDB_SV

// Input File: spi_rgm.spirit

// Number of addrMaps = 1
// Number of regFiles = 1
// Number of registers = 3
// Number of memories = 0


//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 23


class spi_ctrl_c extends uvm_reg;

  rand uvm_reg_field char_len;
  rand uvm_reg_field go_bsy;
  rand uvm_reg_field rx_neg;
  rand uvm_reg_field tx_neg;
  rand uvm_reg_field lsb;
  rand uvm_reg_field ie;
  rand uvm_reg_field ass;

  constraint c_char_len { char_len.value == 7'b0001000; }
  constraint c_tx_neg { tx_neg.value == 1'b1; }
  constraint c_rx_neg { rx_neg.value == 1'b1; }
  constraint c_lsb { lsb.value == 1'b1; }
  constraint c_ie { ie.value == 1'b1; }
  constraint c_ass { ass.value == 1'b1; }
  virtual function void build();
    char_len = uvm_reg_field::type_id::create("char_len");
    char_len.configure(this, 7, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
    go_bsy = uvm_reg_field::type_id::create("go_bsy");
    go_bsy.configure(this, 1, 8, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>8, 1, 1, 1);
    rx_neg = uvm_reg_field::type_id::create("rx_neg");
    rx_neg.configure(this, 1, 9, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>9, 1, 1, 1);
    tx_neg = uvm_reg_field::type_id::create("tx_neg");
    tx_neg.configure(this, 1, 10, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>10, 1, 1, 1);
    lsb = uvm_reg_field::type_id::create("lsb");
    lsb.configure(this, 1, 11, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>11, 1, 1, 1);
    ie = uvm_reg_field::type_id::create("ie");
    ie.configure(this, 1, 12, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>12, 1, 1, 1);
    ass = uvm_reg_field::type_id::create("ass");
    ass.configure(this, 1, 13, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>13, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint char_len.value[6:0];
    coverpoint go_bsy.value[0:0];
    coverpoint rx_neg.value[0:0];
    coverpoint tx_neg.value[0:0];
    coverpoint lsb.value[0:0];
    coverpoint ie.value[0:0];
    coverpoint ass.value[0:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(spi_ctrl_c, uvm_reg_cbs) 
  `uvm_set_super_type(spi_ctrl_c, uvm_reg)
  `uvm_object_utils(spi_ctrl_c)
  function new(input string name="unnamed-spi_ctrl_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : spi_ctrl_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 99


class spi_divider_c extends uvm_reg;

  rand uvm_reg_field divider;

  constraint c_divider { divider.value == 16'b1; }
  virtual function void build();
    divider = uvm_reg_field::type_id::create("divider");
    divider.configure(this, 16, 0, "RW", 0, `UVM_REG_DATA_WIDTH'hffff>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint divider.value[15:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(spi_divider_c, uvm_reg_cbs) 
  `uvm_set_super_type(spi_divider_c, uvm_reg)
  `uvm_object_utils(spi_divider_c)
  function new(input string name="unnamed-spi_divider_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : spi_divider_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 122


class spi_ss_c extends uvm_reg;

  rand uvm_reg_field ss;

  constraint c_ss { ss.value == 8'b1; }
  virtual function void build();
    ss = uvm_reg_field::type_id::create("ss");
    ss.configure(this, 8, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint ss.value[7:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(spi_ss_c, uvm_reg_cbs) 
  `uvm_set_super_type(spi_ss_c, uvm_reg)
  `uvm_object_utils(spi_ss_c)
  function new(input string name="unnamed-spi_ss_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : spi_ss_c

class spi_regfile extends uvm_reg_block;

  rand spi_ctrl_c spi_ctrl;
  rand spi_divider_c spi_divider;
  rand spi_ss_c spi_ss;

  virtual function void build();

    // Now create all registers

    spi_ctrl = spi_ctrl_c::type_id::create("spi_ctrl", , get_full_name());
    spi_divider = spi_divider_c::type_id::create("spi_divider", , get_full_name());
    spi_ss = spi_ss_c::type_id::create("spi_ss", , get_full_name());

    // Now build the registers. Set parent and hdl_paths

    spi_ctrl.configure(this, null, "spi_ctrl_reg");
    spi_ctrl.build();
    spi_divider.configure(this, null, "spi_divider_reg");
    spi_divider.build();
    spi_ss.configure(this, null, "spi_ss_reg");
    spi_ss.build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
    default_map.add_reg(spi_ctrl, `UVM_REG_ADDR_WIDTH'h10, "RW");
    default_map.add_reg(spi_divider, `UVM_REG_ADDR_WIDTH'h14, "RW");
    default_map.add_reg(spi_ss, `UVM_REG_ADDR_WIDTH'h18, "RW");
  endfunction

  `uvm_object_utils(spi_regfile)
  function new(input string name="unnamed-spi_rf");
    super.new(name, UVM_NO_COVERAGE);
  endfunction : new
endclass : spi_regfile

//////////////////////////////////////////////////////////////////////////////
// Address_map definition
//////////////////////////////////////////////////////////////////////////////
class spi_reg_model_c extends uvm_reg_block;

  rand spi_regfile spi_rf;

  function void build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
    spi_rf = spi_regfile::type_id::create("spi_rf", , get_full_name());
    spi_rf.configure(this, "rf2");
    spi_rf.build();
    spi_rf.lock_model();
    default_map.add_submap(spi_rf.default_map, `UVM_REG_ADDR_WIDTH'h800000);
    set_hdl_path_root("apb_spi_addr_map_c");
    this.lock_model();
  endfunction
  `uvm_object_utils(spi_reg_model_c)
  function new(input string name="unnamed-spi_reg_model_c");
    super.new(name, UVM_NO_COVERAGE);
  endfunction
endclass : spi_reg_model_c

`endif // SPI_RDB_SV
