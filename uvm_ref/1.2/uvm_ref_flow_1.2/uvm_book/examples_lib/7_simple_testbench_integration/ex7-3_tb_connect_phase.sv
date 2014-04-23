/****************************************************************
  Example 7-3: UART Controller Testbench Connect Phase

  This is just a code sample.
  The complete example is in: ex7-1_uart_ctrl_tb.sv

  To run:   %  irun -f run.f ex7-1_uart_ctrl_tb.sv
****************************************************************/
function void uart_ctrl_tb::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // Connect TLM ports from monitors to scoreboards
  uart0.Rx.monitor.frame_collected_port.connect(rx_scbd.uart_match);
  apb0.bus_monitor.item_collected_port.connect(rx_scbd.apb_add);
  uart0.Tx.monitor.frame_collected_port.connect(tx_scbd.uart_add);
  apb0.bus_monitor.item_collected_port.connect(tx_scbd.apb_match);

  // Hook up virtual sequencer to interface sequencers
  virtual_sequencer.apb_seqr =  apb0.master.sequencer;
  if (uart0.Tx.get_is_active() == UVM_ACTIVE)
     virtual_sequencer.uart_seqr =  uart0.Tx.sequencer;

endfunction : connect_phase
