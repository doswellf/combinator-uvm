/*-----------------------------------------------------------------
File name     : demo_scoreboard.sv
Developers    : Kathleen Meade
Created       : Tue May 11, 2010
Description   :
Notes         :
-------------------------------------------------------------------
Copyright 2010 (c) Cadence Design Systems
-----------------------------------------------------------------*/

`ifndef DEMO_SCOREBOARD_SV
`define DEMO_SCOREBOARD_SV

//------------------------------------------------------------------------------
//
// CLASS: demo_scoreboard
//
//------------------------------------------------------------------------------

class demo_scoreboard extends uvm_scoreboard;

  // This TLM port is used to connect the scoreboard to the monitor
  uvm_analysis_imp#(uart_frame, demo_scoreboard) item_collected_imp;

  protected bit disable_scoreboard = 0;
  protected int num_writes = 0;
  protected int num_init_reads = 0;
  protected int num_uninit_reads = 0;

  protected int unsigned m_mem_expected[int unsigned];

  // Provide UVM automation and utility methods
  `uvm_component_utils_begin(demo_scoreboard)
    `uvm_field_int(disable_scoreboard, UVM_ALL_ON)
    `uvm_field_int(num_writes, UVM_ALL_ON|UVM_DEC)
    `uvm_field_int(num_init_reads, UVM_ALL_ON|UVM_DEC)
    `uvm_field_int(num_uninit_reads, UVM_ALL_ON|UVM_DEC)
  `uvm_component_utils_end

  // Constructor - required syntax for UVM automation and utilities
  function new (string name, uvm_component parent);
    super.new(name, parent);
    // Construct the TLM interface
    item_collected_imp = new("item_collected_imp", this);
  endfunction : new

  // Additional class methods
  extern virtual function void write(uart_frame frame);
  extern virtual function void memory_verify(input uart_frame frame);
  extern virtual function void report();
   
endclass : demo_scoreboard

  // TLM write() implementation
  function void demo_scoreboard::write(uart_frame frame);
    if(!disable_scoreboard)
      memory_verify(frame);
  endfunction : write

  // memory_verify
  function void demo_scoreboard::memory_verify(input uart_frame frame);
    int unsigned data, exp;
    string op;
    for (int i = 0; i < frame.size; i++) begin
      // Check to see if entry in associative array for this address when read
      // If so, check that frame data matches associative array data.
      if (m_mem_expected.exists(frame.addr + i)) begin
        if (frame.read_write == READ) begin
          op = frame.read_write.name();
          data = frame.data[i];
          `uvm_info(get_type_name(),
            $sformatf("%s to existing address...Checking address : %0h with data : %0h", op, frame.addr, data), UVM_LOW)
          if(m_mem_expected[frame.addr + i] != frame.data[i]) begin
            exp = m_mem_expected[frame.addr + i];
            `uvm_error(get_type_name(),
              $sformatf("Read data mismatch.  Expected : %0h.  Actual : %0h", exp, data), UVM_NONE);
          end
          num_init_reads++;
        end
        if (frame.read_write == WRITE) begin
          op = frame.read_write.name();
          data = frame.data[i];
          `uvm_info(get_type_name(),
              $sformatf("%s to existing address...Updating address : %0h with data : %0h",
              op, frame.addr + i, data), UVM_LOW)
          m_mem_expected[frame.addr + i] = frame.data[i];
          num_writes++;
        end
      end
      // Check to see if entry in associative array for this address
      // If not, update the location regardless if read or write.
      else begin
        op = frame.read_write.name();
        data = frame.data[i];
        `uvm_info(get_type_name(),
          $sformatf("%s to empty address...Updating address : %0h with data : %0h", 
          op, frame.addr + i, data), UVM_LOW)
        m_mem_expected[frame.addr + i] = frame.data[i];
        if(frame.read_write == READ)
          num_uninit_reads++;
        else if (frame.read_write == WRITE)
          num_writes++;
      end
    end
  endfunction : memory_verify

  // report
  function void demo_scoreboard::report();
    if(!disable_scoreboard)
      `uvm_info(get_type_name(),
        $sformatf("Reporting scoreboard information...\n%s", this.sprint()), 
        UVM_LOW)
  endfunction : report

`endif // DEMO_SCOREBOARD_SV

