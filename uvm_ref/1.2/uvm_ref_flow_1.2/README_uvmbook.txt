==========================================================================
A Practical Guide to Adopting the Universal Verification Methodology (UVM)
Second Edition

Book examples

Version 2.0: June 2013
==========================================================================

This collection of UVM examples is a companion to the second edition of the 
UVM book.  The main example used throughout this book is the development of
a testbench for a UART controller device. It is based on the UART module
testbench from the UVM reference flow (available on the contributions area
of www.accelera.org).

The simple examples, interface and module UVCs, and the testbench code are
located as follows:

./uvm_book/examples_lib: a library containing all the book examples
./soc_verification_lib/sv_cb_ex_lib/interface_uvc_lib:
                includes two interface UVCs (APB and UART) that are used
                for the uart controller testbench
./soc_verification_lib/sv_cb_ex_lib/uart_ctrl: includes
                the complete UVM testbench and environment for a UART
                controller design.


For setting up the examples:
============================
   % setenv UVM_HOME <uvm-install-dir>
   % setenv UVM_LIB_PATH $UVM_HOME

For setting up the UVM Reference Example
=========================================
   % setenv UVM_REF_HOME <UVM Reference Flow Install area>
   % setenv SOCV_KIT_HOME ${UVM_REF_HOME}
   % source ${UVM_REF_HOME}/env.csh
   

Using the Examples:
===================
Each chapter of the book has it's own directory under examples_lib.
Each example has a header with the instructions for running on Incisive
Enterprise Simulator (IES) 12.1 or higher.

For most examples, simply execute:
 % irun -uvm <example_name>.sv

These run commands can be easily converted to run on other simulators.

Good luck!

Kathleen Meade and Sharon Rosenberg
