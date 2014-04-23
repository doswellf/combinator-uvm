/**************************************************************************
  Example 9-9: Base Register Sequence for the UART Controller

  This example does not run stand-alone
**************************************************************************/

class base_reg_seq extends uvm_sequence;

  uart_ctrl_reg_model_c model;  // Pointer to the register model

  function new(string name="base_reg_seq");
    super.new(name);
  endfunction

  `uvm_object_utils(base_reg_seq)

 //------------------------------------------------------------------------ 
  // get_model() : use this function to assign the reg model for the sequence
  // Tries to find the model three ways:
  //   1. Checks to see if it was set via a pointer when the seq was created
  //   2. Checks to see if it was set via uvm_config_object
  //   3. Checks to see if it was set via uvm_config_db#(uvm_reg_block)
  //------------------------------------------------------------------------ 
  virtual function void get_model();
    uvm_object temp_object;
    uvm_reg_block temp_reg_block;
    if (model==null) begin
      if (uvm_config_object::get(get_sequencer(), "", "reg_model", temp_object))
         if (!($cast(model, temp_object)))
           `uvm_fatal("BAD_CONFIG",
             "Sequence reg model is not derived from uart_ctrl_reg_model_c.")
      else if (uvm_config_db#(uvm_reg_block)::get(get_sequencer(), "",
              "reg_model", temp_reg_block))
         if (!($cast(model, temp_reg_block)))
           `uvm_fatal("BAD_CONFIG",
             "Sequence reg model is not derived from uart_ctrl_reg_model_c.")
      else
        `uvm_fatal("NO_REG_CONFIG", "Register model is not set. Exiting..")
    end
   endfunction : get_model

  //------------------------------------------------------------------------ 
  // pre_start()  : This task gets called for every sequence.  It calls the
  //            get_model() function to automatically set the register model.
  //------------------------------------------------------------------------ 
  virtual task pre_start();
    get_model();  // get the register model
  endtask : pre_start

  //------------------------------------------------------------------------ 
  // Use pre_body() and post_body() tasks to raise/drop objections.
  //       These tasks only execute for a default sequence 
  //------------------------------------------------------------------------ 
  virtual task pre_body();
     if (starting_phase != null)
        starting_phase.raise_objection(this, {"Running sequence '",
                                              get_full_name(), "'"});
  endtask

  virtual task post_body();
     if (starting_phase != null)
        starting_phase.drop_objection(this, {"Completed sequence '",
                                             get_full_name(), "'"});
  endtask
endclass : base_reg_seq

