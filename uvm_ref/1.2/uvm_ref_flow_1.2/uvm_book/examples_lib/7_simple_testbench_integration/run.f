// UVM Library and Utilities
-uvm

// OR Option 1:Specify a different UVM HOME location
//-uvmhome $UVM_HOME

// OR Option 2: Compile UVM library on your own
//-uvmhome $UVM_HOME
//-uvmnoautocompile
//${UVM_HOME}/src/uvm_pkg.sv
//${UVM_HOME}/src/dpi/uvm_dpi.cc

// Interface UVC Components
-incdir ./apb
-incdir ./uart
-incdir ./uart/sv
./apb/sv/apb_pkg.sv
./uart/sv/uart_pkg.sv

// SV Interfaces
./apb/sv/apb_if.sv
./uart/sv/uart_if.sv

-access rc
+UVM_VERBOSITY=UVM_MEDIUM

-timescale 1ns/1ns
-vtimescale 1ns/1ns
