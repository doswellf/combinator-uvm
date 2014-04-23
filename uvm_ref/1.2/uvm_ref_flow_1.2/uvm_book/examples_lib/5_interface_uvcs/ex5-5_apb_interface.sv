/****************************************************************
  Example 5-5: APB Interface Definition

  To run:   %  irun  ex5-5_apb_interface.sv
****************************************************************/
interface apb_if (input pclk, input presetn);
  // Signals
  logic       [31:0] paddr;
  logic              pwrite;
  logic       [31:0] pwdata;
  logic              penable;
  logic       [15:0] psel;
  logic       [31:0] prdata;
  wire logic         pslverr;
  wire logic         pready;

  // Control flags
  bit                has_checks = 1;
  bit                has_coverage = 1;

// Checkign and coverage (via assertions) would follow here

endinterface : apb_if
