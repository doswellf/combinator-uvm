interface apb_if (input pclock, input preset);
  ... 
  bit                has_checks = 1;
  bit                has_coverage = 1;

// PADDR must not be X or Z when PSEL is asserted
assertPAddrUnknown:assert property (
                  disable iff(!has_checks) 
                  (psel == 0 or !$isunknown(paddr)))
                  else
                    $error("ERR_APB001_PADDR_XZ\n PADDR went to X or Z \
                            when PSEL is asserted");
endinterface : apb_if

class apb_env extends uvm_env;

  protected virtual interface apb_if vif;

  // The following two bits are used to control whether checks and coverage are
  // done both in the bus monitor class and the interface.
  bit checks_enable = 1; 
  bit coverage_enable = 1;

  // Provide implementations of virtual methods such as get_type_name and create
  `uvm_component_utils_begin(apb_env)
    `uvm_field_object(cfg, UVM_DEFAULT)
    `uvm_field_int(checks_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_component_utils_end

  extern virtual task run_phase(uvm_phase phase);
  extern virtual task update_vif_enables();

endclass : apb_env

// update_vif_enables
task apb_env::update_vif_enables();
  vif.has_checks <= checks_enable;
  vif.has_coverage <= coverage_enable;
  forever begin
    @(checks_enable || coverage_enable);
    vif.has_checks <= checks_enable;
    vif.has_coverage <= coverage_enable;
  end
endtask : update_vif_enables

//UVM run_phase()
task apb_env::run_phase(uvm_phase phase);
  fork
    update_vif_enables();
  join
endtask : run_phase
