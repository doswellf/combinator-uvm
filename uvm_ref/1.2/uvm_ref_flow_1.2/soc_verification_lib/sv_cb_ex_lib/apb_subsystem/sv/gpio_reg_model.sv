`ifndef GPIO_RDB_SV
`define GPIO_RDB_SV

// Input File: gpio_rgm.spirit

// Number of addrMaps = 1
// Number of regFiles = 1
// Number of registers = 5
// Number of memories = 0


//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 23


class bypass_mode_c extends uvm_reg;

  rand uvm_reg_field data;

  virtual function void build();
    data = uvm_reg_field::type_id::create("data");
    data.configure(this, 32, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint data.value[31:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(bypass_mode_c, uvm_reg_cbs) 
  `uvm_set_super_type(bypass_mode_c, uvm_reg)
  `uvm_object_utils(bypass_mode_c)
  function new(input string name="unnamed-bypass_mode_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : bypass_mode_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 38


class direction_mode_c extends uvm_reg;

  rand uvm_reg_field data;

  virtual function void build();
    data = uvm_reg_field::type_id::create("data");
    data.configure(this, 32, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint data.value[31:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(direction_mode_c, uvm_reg_cbs) 
  `uvm_set_super_type(direction_mode_c, uvm_reg)
  `uvm_object_utils(direction_mode_c)
  function new(input string name="unnamed-direction_mode_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : direction_mode_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 53


class output_enable_c extends uvm_reg;

  rand uvm_reg_field data;

  virtual function void build();
    data = uvm_reg_field::type_id::create("data");
    data.configure(this, 32, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint data.value[31:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(output_enable_c, uvm_reg_cbs) 
  `uvm_set_super_type(output_enable_c, uvm_reg)
  `uvm_object_utils(output_enable_c)
  function new(input string name="unnamed-output_enable_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : output_enable_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 68


class output_value_c extends uvm_reg;

  rand uvm_reg_field data;

  virtual function void build();
    data = uvm_reg_field::type_id::create("data");
    data.configure(this, 32, 0, "RW", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint data.value[31:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(output_value_c, uvm_reg_cbs) 
  `uvm_set_super_type(output_value_c, uvm_reg)
  `uvm_object_utils(output_value_c)
  function new(input string name="unnamed-output_value_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : output_value_c

//////////////////////////////////////////////////////////////////////////////
// Register definition
//////////////////////////////////////////////////////////////////////////////
// Line Number: 83


class input_value_c extends uvm_reg;

  rand uvm_reg_field data;

  virtual function void build();
    data = uvm_reg_field::type_id::create("data");
    data.configure(this, 32, 0, "RO", 0, `UVM_REG_DATA_WIDTH'h0>>0, 1, 1, 1);
  endfunction

  covergroup value_cg;
    option.per_instance=1;
    coverpoint data.value[31:0];
  endgroup
  
  virtual function void sample_values();
    super.sample_values();
    value_cg.sample();
  endfunction

  `uvm_register_cb(input_value_c, uvm_reg_cbs) 
  `uvm_set_super_type(input_value_c, uvm_reg)
  `uvm_object_utils(input_value_c)
  function new(input string name="unnamed-input_value_c");
    super.new(name, 32, build_coverage(UVM_CVR_FIELD_VALS));
    if(has_coverage(UVM_CVR_FIELD_VALS)) value_cg=new;
  endfunction : new
endclass : input_value_c

class gpio_regfile extends uvm_reg_block;

  rand bypass_mode_c bypass_mode;
  rand direction_mode_c direction_mode;
  rand output_enable_c output_enable;
  rand output_value_c output_value;
  rand input_value_c input_value;

  virtual function void build();

    // Now create all registers

    bypass_mode = bypass_mode_c::type_id::create("bypass_mode", , get_full_name());
    direction_mode = direction_mode_c::type_id::create("direction_mode", , get_full_name());
    output_enable = output_enable_c::type_id::create("output_enable", , get_full_name());
    output_value = output_value_c::type_id::create("output_value", , get_full_name());
    input_value = input_value_c::type_id::create("input_value", , get_full_name());

    // Now build the registers. Set parent and hdl_paths

    bypass_mode.configure(this, null, "bypass_mode_reg");
    bypass_mode.build();
    direction_mode.configure(this, null, "direction_mode_reg");
    direction_mode.build();
    output_enable.configure(this, null, "output_enable_reg");
    output_enable.build();
    output_value.configure(this, null, "output_value_reg");
    output_value.build();
    input_value.configure(this, null, "input_value_reg");
    input_value.build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
    default_map.add_reg(bypass_mode, `UVM_REG_ADDR_WIDTH'h0, "RW");
    default_map.add_reg(direction_mode, `UVM_REG_ADDR_WIDTH'h4, "RW");
    default_map.add_reg(output_enable, `UVM_REG_ADDR_WIDTH'h8, "RW");
    default_map.add_reg(output_value, `UVM_REG_ADDR_WIDTH'hc, "RW");
    default_map.add_reg(input_value, `UVM_REG_ADDR_WIDTH'h10, "RO");
  endfunction

  `uvm_object_utils(gpio_regfile)
  function new(input string name="unnamed-gpio_rf");
    super.new(name, UVM_NO_COVERAGE);
  endfunction : new
endclass : gpio_regfile

//////////////////////////////////////////////////////////////////////////////
// Address_map definition
//////////////////////////////////////////////////////////////////////////////
class gpio_reg_model_c extends uvm_reg_block;

  rand gpio_regfile gpio_rf;

  function void build();
    // Now define address mappings
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
    gpio_rf = gpio_regfile::type_id::create("gpio_rf", , get_full_name());
    gpio_rf.configure(this, "rf3");
    gpio_rf.build();
    gpio_rf.lock_model();
    default_map.add_submap(gpio_rf.default_map, `UVM_REG_ADDR_WIDTH'h820000);
    set_hdl_path_root("apb_gpio_addr_map_c");
    this.lock_model();
  endfunction
  `uvm_object_utils(gpio_reg_model_c)
  function new(input string name="unnamed-gpio_reg_model_c");
    super.new(name, UVM_NO_COVERAGE);
  endfunction
endclass : gpio_reg_model_c

`endif // GPIO_RDB_SV
