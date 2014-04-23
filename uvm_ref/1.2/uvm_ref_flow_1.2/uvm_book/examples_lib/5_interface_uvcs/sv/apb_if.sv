/******************************************************************************
  FILE : apb_if.sv
 ******************************************************************************/
interface apb_if (input pclk, input presetn);
  // Signals
  logic       [31:0] paddr;
  logic              pwrite;
  logic       [31:0] pwdata;
  logic              penable;
  logic       [15:0] psel;
  logic       [31:0] prdata;
  logic         pslverr;
  logic         pready;

  // Control flags
  bit                has_checks = 1;
  bit                has_coverage = 1;

// Coverage and assertions to be implemented here.

endinterface : apb_if
