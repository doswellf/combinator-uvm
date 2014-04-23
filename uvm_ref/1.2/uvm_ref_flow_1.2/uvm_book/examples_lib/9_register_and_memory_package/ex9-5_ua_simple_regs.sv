/*
 Example 9-5:  UART Controller Register File
------------------------------------------------
 This is an incomplete example showing just the Register file and
 address map generated from Input File: ex9-3_ua_simple_regs.xml
------------------------------------------------
 Generated rdb.sv by executing:
   %  runreg -i ex9-3_ua_simple_regs.xml -nc -uvm11a

 To Run:
     %  irun -uvm ex9-5_ua_simple_regs.sv
*/

import uvm_pkg::*;
`include "uvm_macros.svh"


// This file is generated using Cadence iregGen version 12.20.s006 

`ifndef RDB_SV
`define RDB_SV

// Input File: ex9-3_ua_simple_regs.xml

// Number of AddrMaps = 1
// Number of RegFiles = 1
// Number of Registers = 1
// Number of Memories = 0

//////////////////////////////////////////////////////////////////////////////
// Register definition (FILE: ex9-4_ua_lcr.sv)
//////////////////////////////////////////////////////////////////////////////
`include "ex9-4_ua_lcr.sv"
//////////////////////////////////////////////////////////////////////////////
// Register File Definition
//////////////////////////////////////////////////////////////////////////////
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

  virtual function void build();
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
