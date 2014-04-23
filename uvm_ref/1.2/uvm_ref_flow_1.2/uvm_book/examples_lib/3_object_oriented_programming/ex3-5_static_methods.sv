/****************************************************************
  Example 3-5: Static Methods and Attributes

  To run:   %  irun ex3-5_static_methods.sv
****************************************************************/
module top;

typedef enum {RED, BLUE, BLACK, WHITE} color_t;

virtual class car;
  static int counter = 0;  // shared by all instances
  int car_id;
  static local function void increment_counter();
    counter++;
    $display("creating item %0d ...", counter);
  endfunction : increment_counter
  function new();
    increment_counter();  // increment on construction
    car_id = counter;
  endfunction : new
endclass : car

virtual class sports_coupe extends car;  // note that car is a virtual class
  rand color_t color;
  virtual function void print();
    $display("Car #%0d: I'm a %s sports coupe", car_id, color.name());
  endfunction : print
endclass : sports_coupe

class KCMotors_H10 extends sports_coupe;
  virtual function void print();
    $display("Car #%0d: I'm a %s KCMotors_H10", car_id, color.name());
  endfunction : print
endclass : KCMotors_H10

class JRSports_M8 extends sports_coupe;
  virtual function void print();
    $display("Car #%0d: I'm a %s JRSports_M8", car_id, color.name());
  endfunction : print
endclass : JRSports_M8

 sports_coupe cars[]; 
 KCMotors_H10 p1, p2;
 JRSports_M8 f1, f2;

 initial begin
   cars = new[4];
   p1 = new(); p2 = new();
   void'(p1.randomize());
   void'(p2.randomize());
   f1 = new(); f2 = new();
   void'(f1.randomize());
   void'(f2.randomize());
   $cast(cars[0], p1);
   $cast(cars[1], f1);
   $cast(cars[2], p2);
   $cast(cars[3], f2);
   print_all(cars);
 end

 task print_all(sports_coupe cars[]);
   for (int i=0; i<cars.size(); i++)
     cars[i].print();
 endtask : print_all

endmodule : top
