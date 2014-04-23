/*******************************************************************************
  Copyright (c) 2006 Cadence Design Systems, Inc.
  All rights reserved worldwide.
********************************************************************************
  FILE : demo_config.sv
*******************************************************************************/
class demo_config extends uart_config;

  `uvm_object_utils(demo_config)

  function new(string name = "demo_config");
    super.new(name);
    is_rx_active = UVM_ACTIVE;
  endfunction

endclass
