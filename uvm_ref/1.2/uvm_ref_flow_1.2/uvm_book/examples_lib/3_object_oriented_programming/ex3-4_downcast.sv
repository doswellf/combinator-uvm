/****************************************************************
  Example 3-4: Downcast

  To run:   %  irun ex3-4_downcast.sv
****************************************************************/
module top;

typedef enum {RED, BLUE, BLACK, WHITE} color_t;

virtual class sports_coupe;
  int id = 0;
  rand color_t color;
  virtual function void print();
    $display("Car:%0d - I'm a %s sports car", id, color.name());
  endfunction : print
endclass : sports_coupe

class HM_Flyer extends sports_coupe;
  virtual function void fly();
    $display("Car:%0d %m I'm flying!", id);
  endfunction : fly
  virtual function void print();
    $display("Car:%0d I'm a %s HM_Flyer", id, color.name());
  endfunction : print
endclass : HM_Flyer

class KCMotors_H10 extends sports_coupe;
  virtual function void print();
    $display("Car:%0d I'm a %s KCMotors_H10", id, color.name());
  endfunction : print
endclass : KCMotors_H10

task fly_if_you_can(sports_coupe cars[]);
  HM_Flyer this_car;
  for (int i=0; i<cars.size(); i++) begin
    // cars[i].fly();  //a compile-time error
    if ($cast(this_car, cars[i]))
      this_car.fly();
  end
endtask : fly_if_you_can

task print_all(sports_coupe cars[]);
  for (int i=0; i<cars.size(); i++)
    cars[i].print();
endtask : print_all

sports_coupe cars[]; 
KCMotors_H10 kcm1, kcm2;
HM_Flyer     hmf1, hmf2;

 initial begin
   cars = new[4];
   kcm1 = new(); void'(kcm1.randomize());
   kcm2 = new(); void'(kcm2.randomize());
   hmf1 = new(); void'(hmf1.randomize());
   hmf2 = new(); void'(hmf2.randomize());
   $cast(cars[0], kcm1);
   $cast(cars[1], hmf1);
   $cast(cars[2], kcm2);
   $cast(cars[3], hmf2);
   foreach(cars[i]) cars[i].id = i;
   print_all(cars);
   fly_if_you_can(cars);
 end

endmodule : top
