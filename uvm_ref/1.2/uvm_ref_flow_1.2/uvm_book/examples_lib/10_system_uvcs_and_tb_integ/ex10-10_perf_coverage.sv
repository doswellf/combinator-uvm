/**********************************************************************
  Example 10-10: Module UVC Performance-related Coverage


*********************************************************************/
class uart_ctrl_cover extends  uvm_component;

  virtual interface uart_ctrl_if vif;
  bit coverage_enable = 1;

  time rx_time_q[$];
  time rx_clks_delay, clk_period;

  uvm_analysis_imp_apb #(apb_transfer, uart_ctrl_cover) apb_in;
  uvm_analysis_imp_rx #(uart_frame, uart_ctrl_cover) uart_rx_in;

  uart_pkg::uart_config uart_cfg;

  // Required macro for UVM automation and utilities
  `uvm_component_utils_begin(uart_ctrl_cover)
    `uvm_field_int(coverage_enable, UVM_ALL_ON)
  `uvm_component_utils_end

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (!uvm_config_db#(virtual uart_ctrl_if)::get(this, get_full_name(),"vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
      capture_clk_period();
  endtask : run_phase

  covergroup rx_delay_cg;
    clocks : coverpoint rx_clks_delay {
                                       bins ZERO = {0};
                                       bins ONE = {1};
                                       bins TWO = {2};
                                       bins GT_TWO = default;
                                      }
  endgroup

  virtual task capture_clk_period();
      @(vif.clock) clk_period = $time;
      @(vif.clock) clk_period = $time - clk_period;
  endtask : capture_clk_period

  function new(string name , uvm_component parent);
    super.new(name, parent);
    if (coverage_enable) begin
      rx_delay_cg = new();
      rx_delay_cg.set_inst_name ({get_full_name(), ".rx_delay_cg"});
    end
  endfunction

  function void write_rx(uart_frame frame);
    rx_time_q.push_front($time);
  endfunction : write_rx

  function void write_apb(apb_transfer transfer);
    if ((transfer.addr == uart_cfg.fifo_address) &&
        (transfer.direction == APB_READ)) begin
      rx_clks_delay = ($time - rx_time_q.pop_back())/clk_period;
      if (coverage_enable) rx_delay_cg.sample();
    end
  endfunction
endclass : uart_ctrl_cover
