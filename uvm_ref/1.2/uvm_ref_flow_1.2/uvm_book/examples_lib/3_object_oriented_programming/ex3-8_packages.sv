/****************************************************************
  Example : SystemVerilog Packages and Namespace

  To run:   %  irun ex3-8_packages.sv
****************************************************************/

package KCMotors_pkg;
  typedef enum {RED, BLUE, BLACK, WHITE} color_t;
  class sports_coupe; 
    rand color_t color;
    virtual function void print();
      $display("I'm a %s KCMotors sports coupe", color.name());
    endfunction : print
  endclass : sports_coupe
endpackage : KCMotors_pkg

package JRSports_pkg;
  typedef enum {SILVER, GOLD, WHITE} color_t;
  class sports_coupe;
    rand color_t color;
    virtual function void print();
      $display("I'm a %s JRSports sports coupe", color.name());
    endfunction : print
  endclass : sports_coupe
endpackage : JRSports_pkg

module top;
KCMotors_pkg::sports_coupe my_H10;
JRSports_pkg::sports_coupe my_M8;

 initial begin
   my_H10 = new();
   void'(my_H10.randomize());
   my_H10.print();
   my_M8 = new();
   void'(my_M8.randomize());
   my_M8.print();
 end

endmodule : top
