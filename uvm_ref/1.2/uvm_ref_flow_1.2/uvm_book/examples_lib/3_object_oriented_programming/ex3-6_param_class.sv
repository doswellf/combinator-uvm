/****************************************************************
  Example 3-6 : Parameterized Class With Static Field

  To run:   %  irun ex3-6_param_class.sv
****************************************************************/
module top;
class stack #(type T = int);
  static int stacks;
  int id;
  local T items[$];
  task push( T a );   endtask
  task pop (ref T a); endtask
  function new(); stacks++; id = stacks; endfunction 
endclass

stack int_stack = new();             // id: 1
stack #(bit[9:0]) bit_stack = new(); // id: 1
stack #(real) real_stack = new();    // id: 1

initial 
  $display("int_stack.id=%0d   bit_stack.id=%0d   real_stack.id=%0d",
            int_stack.id, bit_stack.id, real_stack.id);

endmodule : top
