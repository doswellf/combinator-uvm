/****************************************************************
  Example 3-9 : Packages and Namespace - no collision

  To run:   %  irun ex3-9_packages.sv
****************************************************************/

package KCMotors_pkg;
  typedef enum {RED, BLUE, BLACK, WHITE} color_t;
  virtual class sports_coupe; // note that car is a virtual class
    rand color_t color;
    virtual function void print();
      $display("I'm a %s KCMotors sports coupe", color.name());
    endfunction : print
  endclass : sports_coupe
  class H10 extends sports_coupe; endclass
endpackage : KCMotors_pkg

package JRSports_pkg;
  typedef enum {SILVER, GOLD, WHITE} color_t;
  virtual class sports_coupe;  // note that car is a virtual class
    rand color_t color;
    virtual function void print();
      $display("I'm a %s JRSports sports coupe", color.name());
    endfunction : print
  endclass : sports_coupe
  class M8 extends sports_coupe; endclass
endpackage : JRSports_pkg

module race;
 import KCMotors_pkg::*;
 import JRSports_pkg::*;

 H10 my_H10;
 M8 my_M8;

 initial begin
   my_H10 = new();
   void'(my_H10.randomize());
   my_H10.print();
   my_M8 = new();
   void'(my_M8.randomize());
   my_M8.print();
 end

endmodule : race
