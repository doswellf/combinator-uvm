//File name   : smc_strobe_lite.v
//Title       : 
//Created     : 1999
//Description : 
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

module smc_strobe_lite  (

                    //inputs

                    sys_clk,
                    n_sys_reset,
                    valid_access,
                    n_read,
                    cs,
                    r_smc_currentstate,
                    smc_nextstate,
                    n_be,
                    r_wele_count,
                    r_wele_store,
                    r_wete_store,
                    r_oete_store,
                    r_ws_count,
                    r_ws_store,
                    smc_done,
                    mac_done,

                    //outputs

                    smc_n_rd,
                    smc_n_ext_oe,
                    smc_busy,
                    n_r_read,
                    r_cs,
                    r_full,
                    n_r_we,
                    n_r_wr);



//Parameters  -  Values in smc_defs.v

 


// I/O

   input                   sys_clk;      //System clock
   input                   n_sys_reset;  //System reset (Active LOW)
   input                   valid_access; //load values are valid if high
   input                   n_read;       //Active low read signal
   input              cs;           //registered chip select
   input [4:0]             r_smc_currentstate;//current state
   input [4:0]             smc_nextstate;//next state  
   input [3:0]             n_be;         //Unregistered Byte strobes
   input [1:0]             r_wele_count; //Write counter
   input [1:0]             r_wete_store; //write strobe trailing edge store
   input [1:0]             r_oete_store; //read strobe
   input [1:0]             r_wele_store; //write strobe leading edge store
   input [7:0]             r_ws_count;   //wait state count
   input [7:0]             r_ws_store;   //wait state store
   input                   smc_done;  //one access completed
   input                   mac_done;  //All cycles in a multiple access
   
   
   output                  smc_n_rd;     // EMI read stobe (Active LOW)
   output                  smc_n_ext_oe; // Enable External bus drivers.
                                                          //  (CS & ~RD)
   output                  smc_busy;  // smc busy
   output                  n_r_read;  // Store RW strobe for multiple
                                                         //  accesses
   output                  r_full;    // Full cycle write strobe
   output [3:0]            n_r_we;    // write enable strobe(active low)
   output                  n_r_wr;    // write strobe(active low)
   output             r_cs;      // registered chip select.   


// Output register declarations

   reg                     smc_n_rd;
   reg                     smc_n_ext_oe;
   reg                r_cs;
   reg                     smc_busy;
   reg                     n_r_read;
   reg                     r_full;
   reg   [3:0]             n_r_we;
   reg                     n_r_wr;

   //wire declarations
   
   wire             smc_mac_done;       //smc_done and  mac_done anded
   wire [2:0]       wait_vaccess_smdone;//concatenated signals for case
   reg              half_cycle;         //used for generating half cycle
                                                //strobes
   


//----------------------------------------------------------------------
// Strobe Generation
//
// Individual Write Strobes
// Write Strobe = Byte Enable & Write Enable
//----------------------------------------------------------------------


//----------------------------------------------------------------------
// signal concatenation for use in case statement
//----------------------------------------------------------------------

   assign smc_mac_done = {smc_done & mac_done};

   assign wait_vaccess_smdone = {1'b0,valid_access,smc_mac_done};
   
   
//----------------------------------------------------------------------
// Store read/write signal for duration of cycle(s)
//----------------------------------------------------------------------

  always @(posedge sys_clk or negedge n_sys_reset)
  
     begin
  
        if (~n_sys_reset)
  
           n_r_read <= 0;
  
        else
          
          begin
             
             casex(wait_vaccess_smdone)
               
               3'b1xx:
                 
                  n_r_read <= n_r_read;
               
               3'b01x:
                 
                  n_r_read <= n_read;
               
               3'b001:
                 
                  n_r_read <= 0;
               
               default:
                 
                  n_r_read <= n_r_read;
               
             endcase        
             
          end
             
     end
   
//----------------------------------------------------------------------
// Store chip selects for duration of cycle(s)--turnaround cycle
//----------------------------------------------------------------------
//----------------------------------------------------------------------
// Store read/write signal for duration of cycle(s)
//----------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
      begin
           
         if (~n_sys_reset)
           
           r_cs <= 1'b0;
         
         else
           
           begin
              
              casex(wait_vaccess_smdone)
                
                 3'b1xx:
                  
                    r_cs <= r_cs ;
                
                 3'b01x:
                  
                    r_cs <= cs ;
                
                 3'b001:
                  
                    r_cs <= 1'b0;
                
                 default:
                  
                    r_cs <= r_cs ;
                
              endcase        
              
           end
         
      end
  

//----------------------------------------------------------------------
// Drive busy output whenever smc active
//----------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
      begin
          
         if (~n_sys_reset)
           
            smc_busy <= 0;
           
           
         else if (smc_nextstate != `SMC_IDLE)
           
            smc_busy <= 1;
           
         else
           
            smc_busy <= 0;
           
     end


//----------------------------------------------------------------------
// Drive OE signal to I/O pins on ASIC
//
// Generate internal, registered Write strobes
// The write strobes are gated with the clock later to generate half 
// cycle strobes
//----------------------------------------------------------------------

  always @(posedge sys_clk or negedge n_sys_reset)
    
     begin
       
        if (~n_sys_reset)
         
           begin
            
              n_r_we <= 4'hF;
              n_r_wr <= 1'h1;
            
           end
       

        else if ((n_read & valid_access & 
                  (smc_nextstate != `SMC_STORE)) |
                 (n_r_read & ~valid_access & 
                  (smc_nextstate != `SMC_STORE)))      
         
           begin
            
              n_r_we <= n_be;
              n_r_wr <= 1'h0;
            
           end
       
        else
         
           begin
            
              n_r_we <= 4'hF;
              n_r_wr <= 1'h1;
            
           end
       
    end
  
//----------------------------------------------------------------------
// Drive OE signal to I/O pins on ASIC -----added by gulbir
//
//----------------------------------------------------------------------
   
   always @(posedge sys_clk or negedge n_sys_reset)
     
     begin
        
        if (~n_sys_reset)
          
          smc_n_ext_oe <= 1;
        
        
        else if ((n_read & valid_access & 
                  (smc_nextstate != `SMC_STORE)) |
                (n_r_read & ~valid_access & 
              (smc_nextstate != `SMC_STORE) & 
                 (smc_nextstate != `SMC_IDLE)))      

           smc_n_ext_oe <= 0;
        
        else
          
           smc_n_ext_oe <= 1;
        
     end
   

//----------------------------------------------------------------------
// Generate half and full signals for write strobes
// A full cycle is required if wait states are added
//----------------------------------------------------------------------
//----------------------------------------------------------------------
// Generate half cycle signals for write strobes
//----------------------------------------------------------------------

always @(r_smc_currentstate or smc_nextstate or
            r_full or 
            r_wete_store or r_ws_store or r_wele_store or 
            r_ws_count or r_wele_count or 
            valid_access or smc_done)
  
  begin     
     
       begin
          
          case (r_smc_currentstate)
            
            `SMC_IDLE:
              
              begin
                 
                     half_cycle = 1'b0;
                 
              end
            
            `SMC_LE:
              
              begin
                 
                 if (smc_nextstate == `SMC_RW)
                   
                   if( ( ( (r_wete_store) == r_ws_count[1:0]) &
                         (r_ws_count[7:2] == 6'd0) &
                         (r_wele_count < 2'd2)
                       ) |
                       (r_ws_count == 8'd0)
                     )
                     
                     half_cycle = 1'b1 & ~r_full;
                 
                   else
                     
                     half_cycle = 1'b0;
                 
                 else
                   
                   half_cycle = 1'b0;
                 
              end
            
            `SMC_RW, `SMC_FLOAT:
              
              begin
                 
                 if (smc_nextstate == `SMC_RW)
                   
                   if (valid_access)

                       
                       half_cycle = 1'b0;
                 
                   else if (smc_done)
                     
                     if( ( (r_wete_store == r_ws_store[1:0]) & 
                           (r_ws_store[7:2] == 6'd0) & 
                           (r_wele_store == 2'd0)
                         ) | 
                         (r_ws_store == 8'd0)
                       )
                       
                       half_cycle = 1'b1 & ~r_full;
                 
                     else
                       
                       half_cycle = 1'b0;
                 
                   else
                     
                     if (r_wete_store == 2'd3)
                       
                       if ( (2'd0 == r_ws_count[1:0]) & 
                            (r_ws_count[7:2] == 6'd1) &
                            (r_wele_count < 2'd2)
                          )
                         
                         half_cycle = 1'b1 & ~r_full;
                 
                       else
                         
                         half_cycle = 1'b0;
                 
                     else
                       
                       if ( ( ( (r_wete_store+2'd1) == r_ws_count[1:0]) & 
                              (r_ws_count[7:2] == 6'd0) & 
                              (r_wele_count < 2'd2)
                            )
                          )
                         
                         half_cycle = 1'b1 & ~r_full;
                 
                       else
                         
                         half_cycle = 1'b0;
                 
                 else
                   
                   half_cycle = 1'b0;
                 
              end
            
            `SMC_STORE:
              
              begin
                 
                 if (smc_nextstate == `SMC_RW)

                   if( ( ( (r_wete_store) == r_ws_count[1:0]) & 
                         (r_ws_count[7:2] == 6'd0) & 
                         (r_wele_count < 2'd2)
                       ) | 
                       (r_ws_count == 8'd0)
                     )
                     
                     half_cycle = 1'b1 & ~r_full;
                 
                   else
                     
                     half_cycle = 1'b0;
                 
                 else
                   
                   half_cycle = 1'b0;
                 
              end
            
            default:
              
              half_cycle = 1'b0;
            
          endcase // r_smc_currentstate
          
       end
     
     end

//----------------------------------------------------------------------
//Full cycle signal generation
//----------------------------------------------------------------------

 always @(posedge sys_clk or negedge n_sys_reset)
             
   begin
      
      if (~n_sys_reset)
        
        begin
           
           r_full <= 1'b0;
           
        end
      
      
           
      else
        
        begin
           
           case (r_smc_currentstate)
             
             `SMC_IDLE:
               
               begin
                  
                  if (smc_nextstate == `SMC_RW)
                    
                         
                         r_full <= 1'b0;
                       
                  else
                        
                       r_full <= 1'b0;
                       
               end
             
          `SMC_LE:
            
          begin
             
             if (smc_nextstate == `SMC_RW)
               
                  if( ( ( (r_wete_store) < r_ws_count[1:0]) | 
                        (r_ws_count[7:2] != 6'd0)
                      ) & 
                      (r_wele_count < 2'd2)
                    )
                    
                    r_full <= 1'b1;
                  
                  else
                    
                    r_full <= 1'b0;
                  
             else
               
                  r_full <= 1'b0;
                  
          end
          
          `SMC_RW, `SMC_FLOAT:
            
            begin
               
               if (smc_nextstate == `SMC_RW)
                 
                 begin
                    
                    if (valid_access)
                      
                           
                           r_full <= 1'b0;
                         
                    else if (smc_done)
                      
                         if( ( ( (r_wete_store < r_ws_store[1:0]) | 
                                 (r_ws_store[7:2] != 6'd0)
                               ) & 
                               (r_wele_store == 2'd0)
                             )
                           )
                           
                           r_full <= 1'b1;
                         
                         else
                           
                           r_full <= 1'b0;
                         
                    else
                      
                      begin
                         
                         if(r_wete_store == 2'd3)
                           
                           if( ( (r_ws_count[7:0] > 8'd4)
                               ) & 
                               (r_wele_count < 2'd2)
                             )
                             
                             r_full <= 1'b1;
                         
                           else
                             
                             r_full <= 1'b0;
                         
                         else if ( ( ( ( (r_wete_store + 2'd1) < 
                                         r_ws_count[1:0]
                                       )
                                     ) |
                                     (r_ws_count[7:2] != 6'd0)
                                   ) & 
                                   (r_wele_count < 2'd2)
                                 )
                           
                           r_full <= 1'b1;
                         
                         else
                           
                           r_full <= 1'b0;
                         
                         
                         
                      end
                    
                 end
               
               else
                 
                    r_full <= 1'b0;
               
            end
             
             `SMC_STORE:
               
               begin
                  
                  if (smc_nextstate == `SMC_RW)

                     if ( ( ( (r_wete_store) < r_ws_count[1:0]) | 
                            (r_ws_count[7:2] != 6'd0)
                          ) & 
                          (r_wele_count == 2'd0)
                        )
                         
                         r_full <= 1'b1;
                       
                       else
                         
                         r_full <= 1'b0;
                       
                  else
                    
                       r_full <= 1'b0;
                       
               end
             
             default:
               
                  r_full <= 1'b0;
                  
           endcase // r_smc_currentstate
           
             end
      
   end
 
//----------------------------------------------------------------------
// Generate Read Strobe
//----------------------------------------------------------------------
 
  always @(posedge sys_clk or negedge n_sys_reset)
  
  begin
     
     if (~n_sys_reset)
  
        smc_n_rd <= 1'h1;
      
      
     else if (smc_nextstate == `SMC_RW)
  
     begin
  
        if (valid_access)
  
        begin
  
  
              smc_n_rd <= n_read;
  
  
        end
  
        else if ((r_smc_currentstate == `SMC_LE) | 
                    (r_smc_currentstate == `SMC_STORE))

        begin
           
           if( (r_oete_store < r_ws_store[1:0]) | 
               (r_ws_store[7:2] != 6'd0) |
               ( (r_oete_store == r_ws_store[1:0]) & 
                 (r_ws_store[7:2] == 6'd0)
               ) |
               (r_ws_store == 8'd0) 
             )
             
             smc_n_rd <= n_r_read;
           
           else
             
             smc_n_rd <= 1'b1;
           
        end
        
        else
  
        begin

           if( ( (r_oete_store) < r_ws_count[1:0]) | 
               (r_ws_count[7:2] != 6'd0) |
               (r_ws_count == 8'd0) 
             )
             
              smc_n_rd <= n_r_read;
           
           else

              smc_n_rd <= 1'b1;
         
        end
        
     end
     
     else
       
        smc_n_rd <= 1'b1;
     
  end
   
   
 
endmodule


