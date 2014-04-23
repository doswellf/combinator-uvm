/**************************************************************************
  Example 9-10: UART Controller Register Configuration Sequence

  This example does not run stand-alone
**************************************************************************/

class uart_ctrl_config_reg_seq extends base_reg_seq;

  `uvm_object_utils(uart_ctrl_config_reg_seq)
  function new(string name="uart_ctrl_config_reg_seq");
    super.new(name);
  endfunction

  virtual task body();
    uvm_status_e status;
    `uvm_info("REG_SEQ", "Executing Sequence", UVM_HIGH)
    // Line Control Register, Set Divisor Latch Access = 1
    model.uart_ctrl_rf.ua_lcr.write(status, 'h8f);
    // Divisor Latch Byte 1 = 1
    model.uart_ctrl_rf.ua_div_latch0.write(status, 'h01);
    // Divisor Latch Byte 2 = 0
    model.uart_ctrl_rf.ua_div_latch1.write(status, 'h00);
    // Line Control Register, Set Divisor Latch Access = 0
    model.uart_ctrl_rf.ua_lcr.write(status, 'h0f);
    `uvm_info("REG_SEQ", "Sequence Completed", UVM_HIGH)
  endtask

endclass : uart_ctrl_config_reg_seq
