/****************************************************************
  Example 4-16: Usage of `uvm_analysis_imp_decl macros

  To run:   %  irun -uvm ex4-16_decl_macros.sv
  Or:       %  irun -uvmhome $UVM_HOME ex4-16_decl_macros.sv
****************************************************************/
package my_uvc_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `include "simple_packet.sv" 
  // Other files for this package
endpackage : my_uvc_pkg

package scoreboard_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import my_uvc_pkg::*;  // includes simple_packet

  // TLM Port Declarations Macros
  `uvm_analysis_imp_decl(_inport1)
  `uvm_analysis_imp_decl(_inport2)
  `uvm_analysis_imp_decl(_outport1)
  `uvm_analysis_imp_decl(_outport2)

  class myscoreboard extends uvm_component;

    uvm_analysis_imp_inport1 #(simple_packet, myscoreboard) in_export_1;
    uvm_analysis_imp_inport2 #(simple_packet, myscoreboard) in_export_2;
    uvm_analysis_imp_outport1 #(simple_packet, myscoreboard) out_export_1;
    uvm_analysis_imp_outport2 #(simple_packet, myscoreboard) out_export_2;

    simple_packet packet_fifo1[$], packet_fifo2[$];

    `uvm_component_utils(myscoreboard)
    function new(string name, uvm_component parent);
      super.new(name, parent);
      in_export_1 = new("in_export_1", this);
      in_export_2 = new("in_export_2", this);
      out_export_1 = new("out_export_1", this);
      out_export_1 = new("out_export_1", this);
    endfunction : new

    function void write_inport1(simple_packet packet);
       packet_fifo1.push_back(packet);
    endfunction : write_inport1

    function void write_inport2(simple_packet packet);
       packet_fifo2.push_back(packet);
    endfunction : write_inport2

    function void write_outport1(simple_packet packet);
       simple_packet expected;
       expected = packet_fifo1.pop_front();
       expected.transform1();  // execute some transformation function
       if (!expected.compare(packet))
         `uvm_error("SBFAIL", $sformatf("Expected: %s  Got: %s", expected.sprint(), packet.sprint()))
    endfunction : write_outport1

    function void write_outport2(simple_packet packet);
       simple_packet expected;
       expected = packet_fifo2.pop_front();
       expected.transform2();  // execute a different transformation
       if (!expected.compare(packet))
         `uvm_error("SBFAIL", $sformatf("Expected: %s  Got: %s", expected.sprint(), packet.sprint()))
    endfunction : write_outport2
  endclass : myscoreboard
endpackage : scoreboard_pkg
