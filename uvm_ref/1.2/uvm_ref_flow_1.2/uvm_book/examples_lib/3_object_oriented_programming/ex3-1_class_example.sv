/****************************************************************
  Example 3-1: SystemVerilog Class Example

  To run:   %  irun ex3-1_class_example.sv
****************************************************************/
class car;  // class definition
  typedef enum {AUTOMATIC, MANUAL} transmission_type;
  // Internal car attributes
  int m_num_doors;      // number of doors
  bit m_is_locked[];     // locked state per door
  transmission_type m_trans;  // transmission type
  // Public interfaces to car attributes
  task drive_forward();
   $display("Car with transmission:%s is driving forward", m_trans.name());
  endtask : drive_forward 
  task unlock_door(input int door); m_is_locked[door] = 0; endtask
  task lock_door(input int door); m_is_locked[door] = 1; endtask
  task open_door(input int door);
     if (m_is_locked[door] == 1)
        $display ("Must unlock door[%0d] first", door); 
     else $display("Door[%0d] is now open", door);
  endtask
  function new(input int num_doors=2, 
               input transmission_type trans=AUTOMATIC);
    m_trans = trans;
    m_num_doors = num_doors;
    m_is_locked = new[num_doors];
    foreach(m_is_locked[i]) m_is_locked[i] = 1;
  endfunction 
endclass : car

module top;
  car my_car;
  initial begin
    my_car = new(4);
    my_car.open_door(0);
    my_car.unlock_door(0);
    my_car.open_door(0);
    my_car.drive_forward();
  end
endmodule 
