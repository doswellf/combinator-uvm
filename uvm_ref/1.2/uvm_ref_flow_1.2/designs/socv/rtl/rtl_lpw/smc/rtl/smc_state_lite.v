//File name   : smc_state_lite.v
//Title       : 
//Created     : 1999
//
//Description : SMC State Machine
//            : Static Memory Controller
//Notes       : 
//----------------------------------------------------------------------
//   Copyright 1999-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

`include "smc_defs_lite.v"

//state machine for smc
  module smc_state_lite  (
                     //inputs
  
                     sys_clk,
                     n_sys_reset,
                     new_access,
                     r_cste_count,
                     r_csle_count,
                     r_ws_count,
                     mac_done,
                     n_read,
                     n_r_read,
                     r_csle_store,
                     r_oete_store,
                     cs,
                     r_cs,
             
                     //outputs
  
                     r_smc_currentstate,
                     smc_nextstate,
                     cste_enable,
                     ws_enable,
                     smc_done,
                     valid_access,
                     le_enable,
                     latch_data,
                     smc_idle);
   
   
   
//Parameters  -  Values in smc_defs.v



// I/O

  input            sys_clk;           // AHB System clock
  input            n_sys_reset;       // AHB System reset (Active LOW)
  input            new_access;        // New AHB valid access to smc 
                                          // detected
  input [1:0]      r_cste_count;      // Chip select TE counter
  input [1:0]      r_csle_count;      // chip select leading edge count
  input [7:0]      r_ws_count; // wait state count
  input            mac_done;          // All cycles in a multiple access
  input            n_read;            // Active low read signal
  input            n_r_read;          // Store RW state for multiple 
                                           // accesses
  input [1:0]      r_csle_store;      // Chip select LE store
  input [1:0]      r_oete_store;      // Read strobe TE end time before CS
  input       cs;        // chip selects
  input       r_cs;      // registered chip selects

  output [4:0]      r_smc_currentstate;// Synchronised SMC state machine
  output [4:0]      smc_nextstate;     // State Machine 
  output            cste_enable;       // Enable CS Trailing Edge counter
  output            ws_enable;         // Wait state counter enable
  output            smc_done;          // one access completed
  output            valid_access;      // load values are valid if high
  output            le_enable;         // Enable all Leading Edge 
                                           // counters
  output            latch_data;        // latch_data is used by the 
                                           // MAC block
                                     //  to store read data if CSTE > 0
  output            smc_idle;          // idle state



// Output register declarations

  reg [4:0]    smc_nextstate;     // SMC state machine (async encoding)
  reg [4:0]    r_smc_currentstate;// Synchronised SMC state machine
  reg          ws_enable;         // Wait state counter enable
  reg          cste_enable;       // Chip select counter enable
  reg          smc_done;         // Asserted during last cycle of access
  reg          valid_access;      // load values are valid if high
  reg          le_enable;         // Enable all Leading Edge counters
  reg          latch_data;        // latch_data is used by the MAC block
  reg          smc_idle;          // idle state
  


//----------------------------------------------------------------------
// Main code
//----------------------------------------------------------------------

//----------------------------------------------------------------------
// SMC state machine
//----------------------------------------------------------------------
// Generates the required timings for the External Memory Interface.
// If back-to-back accesses are required the state machine will bypass
// the idle state, thus maintaining the chip select ouput.
//----------------------------------------------------------------------



//----------------------------------------------------------------------
// Generate internal idle signal used by AHB IF
//----------------------------------------------------------------------

  always @(smc_nextstate)
  
  begin
   
     if (smc_nextstate == `SMC_IDLE)
     
        smc_idle = 1'b1;
   
     else
       
        smc_idle = 1'b0;
   
  end
  


//----------------------------------------------------------------------
// Generate internal done signal
//----------------------------------------------------------------------
  
  always @(r_smc_currentstate or r_cste_count or r_ws_count)
  
  begin
   
     if ( ( (r_smc_currentstate == `SMC_RW) &
            (r_ws_count == 8'd0) &
            (r_cste_count == 2'd0)
          ) |
          ( (r_smc_currentstate == `SMC_FLOAT)  &
            (r_cste_count == 2'd0)
          )
        )
       
        smc_done = 1'b1;
   
   else
     
      smc_done = 1'b0;
   
  end



//----------------------------------------------------------------------
// latch_data is used by the MAC block to store read data if CSTE > 0
//----------------------------------------------------------------------

  always @(r_smc_currentstate or r_ws_count or r_oete_store)
  
  begin
   
     if ( (r_smc_currentstate == `SMC_RW) &
          (r_ws_count[1:0] >= r_oete_store) &
          (r_ws_count[7:2] == 6'd0)
        )
     
       latch_data = 1'b1;
   
     else
       
       latch_data = 1'b0;
   
    end
  


//----------------------------------------------------------------------
// Generatecounter enable signals
//----------------------------------------------------------------------
  
  always @(r_smc_currentstate or r_csle_count or
       smc_nextstate or valid_access)
  begin
     if(valid_access)
     begin
        if ((smc_nextstate == `SMC_RW)         &
            (r_smc_currentstate != `SMC_STORE) &
            (r_smc_currentstate != `SMC_LE))
  
          ws_enable = 1'b1;
  
        else
  
          ws_enable = 1'b0;
  
     end
     
     else
       
     begin
  
        if ((smc_nextstate == `SMC_RW) & 
            (r_csle_count == 2'd0) & 
            (r_smc_currentstate != `SMC_STORE) &
            (r_smc_currentstate != `SMC_LE))

           ws_enable = 1'b1;
   
        else
  
           ws_enable = 1'b0;
  
     end
     
  end
   
//----------------------------------------------------------------------
//le_enable
//----------------------------------------------------------------------

  always @(r_smc_currentstate or smc_nextstate)
  
  begin
  
     if (((smc_nextstate == `SMC_LE) | (smc_nextstate == `SMC_RW) ) &
         (r_smc_currentstate != `SMC_STORE) )
  
        le_enable = 1'b1;
  
     else
  
        le_enable = 1'b0;  
  
    end
  
//----------------------------------------------------------------------
//cste_enable
//----------------------------------------------------------------------
  
  always @(smc_nextstate)
  
  begin
     if (smc_nextstate == `SMC_FLOAT)
    
        cste_enable = 1'b1;
   
     else
  
        cste_enable = 1'b0;
  
  end
  


   


//----------------------------------------------------------------------
// valid access is HIGH if new cycle is waiting 
// to start & the last is complete
//----------------------------------------------------------------------
  
  always @(r_smc_currentstate or new_access or r_ws_count or
                                     smc_nextstate or mac_done)
  
  begin
     
     if (new_access & mac_done &
         (((r_smc_currentstate == `SMC_RW) & 
           (smc_nextstate == `SMC_RW) & 
           (r_ws_count == 8'd0))                                |
          ((r_smc_currentstate == `SMC_FLOAT) & 
           (smc_nextstate == `SMC_IDLE) ) |
          ((r_smc_currentstate == `SMC_FLOAT) & 
           (smc_nextstate == `SMC_LE)   ) |
          ((r_smc_currentstate == `SMC_FLOAT) & 
           (smc_nextstate == `SMC_RW)   ) |
          ((r_smc_currentstate == `SMC_FLOAT) & 
           (smc_nextstate == `SMC_STORE)) |
          ((r_smc_currentstate == `SMC_RW)    & 
           (smc_nextstate == `SMC_STORE)) |
          ((r_smc_currentstate == `SMC_RW)    & 
           (smc_nextstate == `SMC_IDLE) ) |
          ((r_smc_currentstate == `SMC_RW)    & 
           (smc_nextstate == `SMC_LE)   ) |
          ((r_smc_currentstate == `SMC_IDLE) ) )  )    
       
       valid_access = 1'b1;
     
     else
       
       valid_access = 1'b0;
  
  end
  
  
  
//----------------------------------------------------------------------
// SMC State Machine
//----------------------------------------------------------------------

 always @(r_smc_currentstate or new_access or 
          cs or r_csle_count or r_cste_count or r_ws_count or mac_done 
          or r_cs or n_read or n_r_read or r_csle_store)
  begin
   
   case (r_smc_currentstate)
  
     `SMC_IDLE :
  
        if (new_access )
 
           smc_nextstate = `SMC_STORE;
  
        else
  
        begin
  
  
           begin

              if (new_access )
  
                 smc_nextstate = `SMC_RW;

              else
  
                 smc_nextstate = `SMC_IDLE;

           end
          
        end

     `SMC_STORE   :

        if ((r_csle_count != 2'd0))

           smc_nextstate = `SMC_LE;

        else

        begin
           
           if ( (r_csle_count == 2'd0))

              smc_nextstate = `SMC_RW;
           
           else
             
              smc_nextstate = `SMC_STORE;

        end      

     `SMC_LE   :
  
        if (r_csle_count < 2'd2)
  
           smc_nextstate = `SMC_RW;
  
        else
  
           smc_nextstate = `SMC_LE;
  
     `SMC_RW   :
  
     begin
          
        if ((r_ws_count == 8'd0) & 
            (r_cste_count != 2'd0))
  
           smc_nextstate = `SMC_FLOAT;
          
        else if ((r_ws_count == 8'd0) &
                 (r_cste_count == 2'h0) &
                 mac_done & ~new_access)

           smc_nextstate = `SMC_IDLE;
          
        else if ((~mac_done & (r_csle_store != 2'd0)) &
                 (r_ws_count == 8'd0))
 
           smc_nextstate = `SMC_LE;

        
        else
          
        begin
  
           if  ( ((n_read != n_r_read) | ((cs != r_cs) & ~n_r_read)) & 
                  new_access & mac_done &
                 (r_ws_count == 8'd0))   
             
              smc_nextstate = `SMC_STORE;
           
           else
             
              smc_nextstate = `SMC_RW;
           
        end
        
     end
  
     `SMC_FLOAT   :
        if (~ mac_done                               & 
            (( & new_access) | 
             ((r_csle_store == 2'd0)            &
              ~new_access)) &  (r_cste_count == 2'd0) )
  
           smc_nextstate = `SMC_RW;
  
        else if (new_access                              & 
                 (( new_access) |
                  ((r_csle_store == 2'd0)            & 
                   ~new_access)) & (r_cste_count == 2'd0) )

        begin
  
           if  (((n_read != n_r_read) | ((cs != r_cs) & ~n_r_read)))   
  
              smc_nextstate = `SMC_STORE;
  
           else
  
              smc_nextstate = `SMC_RW;
  
        end
     
        else
          
        begin
  
           if ((~mac_done & (r_csle_store != 2'd0)) & 
               (r_cste_count < 2'd1))
  
              smc_nextstate = `SMC_LE;

           
           else
             
           begin
           
              if (r_cste_count == 2'd0)
             
                 smc_nextstate = `SMC_IDLE;
           
              else
  
                 smc_nextstate = `SMC_FLOAT;
  
           end
           
        end
     
     default   :
       
       smc_nextstate = `SMC_IDLE;
     
   endcase
     
  end
   
//----------------------------------------------------------------------
//sequential process of state machine
//----------------------------------------------------------------------

  always @(posedge sys_clk or negedge n_sys_reset)
  
  begin
  
     if (~n_sys_reset)
  
        r_smc_currentstate <= `SMC_IDLE;
  
  
     else   
       
        r_smc_currentstate <= smc_nextstate;
  
  
  end

   

   
endmodule


