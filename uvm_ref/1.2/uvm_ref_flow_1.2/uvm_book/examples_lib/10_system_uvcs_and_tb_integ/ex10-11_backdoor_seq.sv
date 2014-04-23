/**************************************************************************
  Example 10-11: Configuration Sequence with Configurable Backdoor Access

***************************************************************************/
class uart_ctrl_config_bd_seq extends base_reg_seq;

 `uvm_object_utils(uart_ctrl_config_bd_seq)
  function new(string name="uart_ctrl_config_bd_seq");
      super.new(name);
  endfunction : new

  virtual task body();
    uvm_status_e status;
    uvm_path_e   path;
    bit is_backdoor = 0;  // FLAG for backdoor access
    // COMMAND-LINE overwrite:  +uvm_set_config_int="*,is_backdoor,1"
    void'(uvm_config_int::get(uvm_root::get(), get_full_name(),
             "is_backdoor", is_backdoor));
    path = (is_backdoor == 0) ? UVM_FRONTDOOR : UVM_BACKDOOR;
    `uvm_info("REG_CONFIG", $sformatf("Configuration(%s) Starting...", path.name()), UVM_LOW)
    // Line Control Register, set Divisor Latch Access = 1
    model.uart_ctrl_rf.ua_lcr.write(status, 'h8f, path);
    // Divisor Latch Byte 1 = 1
    model.uart_ctrl_rf.ua_div_latch0.write(status, 'h01, path);
    // Divisor Latch Byte 2 = 0
    model.uart_ctrl_rf.ua_div_latch1.write(status, 'h00, path);
    // Line Control Register, set Divisor Latch Access = 0
    model.uart_ctrl_rf.ua_lcr.write(status, 'h0f, path);
  endtask : body

endclass : uart_ctrl_config_bd_seq
