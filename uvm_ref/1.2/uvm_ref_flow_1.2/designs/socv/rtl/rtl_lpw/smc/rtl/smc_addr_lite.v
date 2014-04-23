//File name   : smc_addr_lite.v
//Title       : 
//Created     : 1999
//Description : This block registers the address and chip select
//              lines for the current access. The address may only
//              driven for one cycle by the AHB. If multiple
//              accesses are required the bottom two address bits
//              are modified between cycles depending on the current
//              transfer and bus size.
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

//


`include "smc_defs_lite.v"

// address decoder

module smc_addr_lite    (
                    //inputs

                    sys_clk,
                    n_sys_reset,
                    valid_access,
                    r_num_access,
                    v_bus_size,
                    v_xfer_size,
                    cs,
                    addr,
                    smc_done,
                    smc_nextstate,


                    //outputs

                    smc_addr,
                    smc_n_be,
                    smc_n_cs,
                    n_be);



// I/O

   input                    sys_clk;      //AHB System clock
   input                    n_sys_reset;  //AHB System reset 
   input                    valid_access; //Start of new cycle
   input [1:0]              r_num_access; //MAC counter
   input [1:0]              v_bus_size;   //bus width for current access
   input [1:0]              v_xfer_size;  //Transfer size for current 
                                              // access
   input               cs;           //Chip (Bank) select(internal)
   input [31:0]             addr;         //Internal address
   input                    smc_done;     //Transfer complete (state 
                                              // machine)
   input [4:0]              smc_nextstate;//Next state 

   
   output [31:0]            smc_addr;     //External Memory Interface 
                                              //  address
   output [3:0]             smc_n_be;     //EMI byte enables 
   output              smc_n_cs;     //EMI Chip Selects 
   output [3:0]             n_be;         //Unregistered Byte strobes
                                             // used to genetate 
                                             // individual write strobes

// Output register declarations
   
   reg [31:0]                  smc_addr;
   reg [3:0]                   smc_n_be;
   reg                    smc_n_cs;
   reg [3:0]                   n_be;
   
   
   // Internal register declarations
   
   reg [1:0]                  r_addr;           // Stored Address bits 
   reg                   r_cs;             // Stored CS
   reg [1:0]                  v_addr;           // Validated Address
                                                     //  bits
   reg [7:0]                  v_cs;             // Validated CS
   
   wire                       ored_v_cs;        //oring of v_sc
   wire [4:0]                 cs_xfer_bus_size; //concatenated bus and 
                                                  // xfer size
   wire [2:0]                 wait_access_smdone;//concatenated signal
   

// Main Code
//----------------------------------------------------------------------
// Address Store, CS Store & BE Store
//----------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
     begin
        
        if (~n_sys_reset)
          
           r_cs <= 1'b0;
        
        
        else if (valid_access)
          
           r_cs <= cs ;
        
        else
          
           r_cs <= r_cs ;
        
     end

//----------------------------------------------------------------------
//v_cs generation   
//----------------------------------------------------------------------
   
   always @(cs or r_cs or valid_access )
     
     begin
        
        if (valid_access)
          
           v_cs = cs ;
        
        else
          
           v_cs = r_cs;
        
     end

//----------------------------------------------------------------------

   assign wait_access_smdone = {1'b0,valid_access,smc_done};

//----------------------------------------------------------------------
//smc_addr generation
//----------------------------------------------------------------------

  always @(posedge sys_clk or negedge n_sys_reset)
    
    begin
      
      if (~n_sys_reset)
        
         smc_addr <= 32'h0;
      
      else

        begin

          casex(wait_access_smdone)
             3'b1xx :

               smc_addr <= smc_addr;
                        //valid_access 
             3'b01x : begin
               // Set up address for first access
               // little-endian from max address downto 0
               // big-endian from 0 upto max_address
               smc_addr [31:2] <= addr [31:2];

               casez( { v_xfer_size, v_bus_size, 1'b0 } )

               { `XSIZ_32, `BSIZ_32, 1'b? } : smc_addr[1:0] <= 2'b00;
               { `XSIZ_32, `BSIZ_16, 1'b0 } : smc_addr[1:0] <= 2'b10;
               { `XSIZ_32, `BSIZ_16, 1'b1 } : smc_addr[1:0] <= 2'b00;
               { `XSIZ_32, `BSIZ_8, 1'b0 } :  smc_addr[1:0] <= 2'b11;
               { `XSIZ_32, `BSIZ_8, 1'b1 } :  smc_addr[1:0] <= 2'b00;
               { `XSIZ_16, `BSIZ_32, 1'b? } : smc_addr[1:0] <= {addr[1],1'b0};
               { `XSIZ_16, `BSIZ_16, 1'b? } : smc_addr[1:0] <= {addr[1],1'b0};
               { `XSIZ_16, `BSIZ_8, 1'b0 } :  smc_addr[1:0] <= {addr[1],1'b1};
               { `XSIZ_16, `BSIZ_8, 1'b1 } :  smc_addr[1:0] <= {addr[1],1'b0};
               { `XSIZ_8, 2'b??, 1'b? } :     smc_addr[1:0] <= addr[1:0];
               default:                       smc_addr[1:0] <= addr[1:0];

               endcase

             end
              
             3'b001 : begin

                // set up addresses fro subsequent accesses
                // little endian decrements according to access no.
                // bigendian increments as access no decrements

                  smc_addr[31:2] <= smc_addr[31:2];
                  
               casez( { v_xfer_size, v_bus_size, 1'b0 } )

               { `XSIZ_32, `BSIZ_32, 1'b? } : smc_addr[1:0] <= 2'b00;
               { `XSIZ_32, `BSIZ_16, 1'b0 } : smc_addr[1:0] <= 2'b00;
               { `XSIZ_32, `BSIZ_16, 1'b1 } : smc_addr[1:0] <= 2'b10;
               { `XSIZ_32, `BSIZ_8,  1'b0 } : 
                  case( r_num_access ) 
                  2'b11:   smc_addr[1:0] <= 2'b10;
                  2'b10:   smc_addr[1:0] <= 2'b01;
                  2'b01:   smc_addr[1:0] <= 2'b00;
                  default: smc_addr[1:0] <= 2'b11;
                  endcase
               { `XSIZ_32, `BSIZ_8, 1'b1 } :  
                  case( r_num_access ) 
                  2'b11:   smc_addr[1:0] <= 2'b01;
                  2'b10:   smc_addr[1:0] <= 2'b10;
                  2'b01:   smc_addr[1:0] <= 2'b11;
                  default: smc_addr[1:0] <= 2'b00;
                  endcase
               { `XSIZ_16, `BSIZ_32, 1'b? } : smc_addr[1:0] <= {r_addr[1],1'b0};
               { `XSIZ_16, `BSIZ_16, 1'b? } : smc_addr[1:0] <= {r_addr[1],1'b0};
               { `XSIZ_16, `BSIZ_8, 1'b0 } :  smc_addr[1:0] <= {r_addr[1],1'b0};
               { `XSIZ_16, `BSIZ_8, 1'b1 } :  smc_addr[1:0] <= {r_addr[1],1'b1};
               { `XSIZ_8, 2'b??, 1'b? } :     smc_addr[1:0] <= r_addr[1:0];
               default:                       smc_addr[1:0] <= r_addr[1:0];

               endcase
                 
            end
            
            default :

               smc_addr <= smc_addr;
            
          endcase // casex(wait_access_smdone)
           
        end
      
    end
  


//----------------------------------------------------------------------
// Generate Chip Select Output 
//----------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
     begin
        
        if (~n_sys_reset)
          
          begin
             
             smc_n_cs <= 1'b0;
             
          end
        
        
        else if  (smc_nextstate == `SMC_RW)
          
           begin
             
              if (valid_access)
               
                 smc_n_cs <= ~cs ;
             
              else
               
                 smc_n_cs <= ~r_cs ;

           end
        
        else
          
           smc_n_cs <= 1;
           
     end



//----------------------------------------------------------------------
// Latch LSB of addr
//----------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
     begin
        
        if (~n_sys_reset)
          
           r_addr <= 2'd0;
        
        
        else if (valid_access)
          
           r_addr <= addr[1:0];
        
        else
          
           r_addr <= r_addr;
        
     end
   


//----------------------------------------------------------------------
// Validate LSB of addr with valid_access
//----------------------------------------------------------------------

   always @(r_addr or valid_access or addr)
     
      begin
        
         if (valid_access)
           
            v_addr = addr[1:0];
         
         else
           
            v_addr = r_addr;
         
      end
//----------------------------------------------------------------------
//cancatenation of signals
//----------------------------------------------------------------------
                               //check for v_cs = 0
   assign ored_v_cs = |v_cs;   //signal concatenation to be used in case
   
//----------------------------------------------------------------------
// Generate (internal) Byte Enables.
//----------------------------------------------------------------------

   always @(v_cs or v_xfer_size or v_bus_size or v_addr )
     
     begin

       if ( |v_cs == 1'b1 ) 
        
         casez( {v_xfer_size, v_bus_size, 1'b0, v_addr[1:0] } )
          
         {`XSIZ_8, `BSIZ_8, 1'b?, 2'b??} : n_be = 4'b1110; // Any on RAM B0
         {`XSIZ_8, `BSIZ_16,1'b0, 2'b?0} : n_be = 4'b1110; // B2 or B0 = RAM B0
         {`XSIZ_8, `BSIZ_16,1'b0, 2'b?1} : n_be = 4'b1101; // B3 or B1 = RAM B1
         {`XSIZ_8, `BSIZ_16,1'b1, 2'b?0} : n_be = 4'b1101; // B2 or B0 = RAM B1
         {`XSIZ_8, `BSIZ_16,1'b1, 2'b?1} : n_be = 4'b1110; // B3 or B1 = RAM B0
         {`XSIZ_8, `BSIZ_32,1'b0, 2'b00} : n_be = 4'b1110; // B0 = RAM B0
         {`XSIZ_8, `BSIZ_32,1'b0, 2'b01} : n_be = 4'b1101; // B1 = RAM B1
         {`XSIZ_8, `BSIZ_32,1'b0, 2'b10} : n_be = 4'b1011; // B2 = RAM B2
         {`XSIZ_8, `BSIZ_32,1'b0, 2'b11} : n_be = 4'b0111; // B3 = RAM B3
         {`XSIZ_8, `BSIZ_32,1'b1, 2'b00} : n_be = 4'b0111; // B0 = RAM B3
         {`XSIZ_8, `BSIZ_32,1'b1, 2'b01} : n_be = 4'b1011; // B1 = RAM B2
         {`XSIZ_8, `BSIZ_32,1'b1, 2'b10} : n_be = 4'b1101; // B2 = RAM B1
         {`XSIZ_8, `BSIZ_32,1'b1, 2'b11} : n_be = 4'b1110; // B3 = RAM B0
         {`XSIZ_16,`BSIZ_8, 1'b?, 2'b??} : n_be = 4'b1110; // Any on RAM B0
         {`XSIZ_16,`BSIZ_16,1'b?, 2'b??} : n_be = 4'b1100; // Any on RAMB10
         {`XSIZ_16,`BSIZ_32,1'b0, 2'b0?} : n_be = 4'b1100; // B10 = RAM B10
         {`XSIZ_16,`BSIZ_32,1'b0, 2'b1?} : n_be = 4'b0011; // B23 = RAM B23
         {`XSIZ_16,`BSIZ_32,1'b1, 2'b0?} : n_be = 4'b0011; // B10 = RAM B23
         {`XSIZ_16,`BSIZ_32,1'b1, 2'b1?} : n_be = 4'b1100; // B23 = RAM B10
         {`XSIZ_32,`BSIZ_8, 1'b?, 2'b??} : n_be = 4'b1110; // Any on RAM B0
         {`XSIZ_32,`BSIZ_16,1'b?, 2'b??} : n_be = 4'b1100; // Any on RAM B10
         {`XSIZ_32,`BSIZ_32,1'b?, 2'b??} : n_be = 4'b0000; // Any on RAM B3210
         default                         : n_be = 4'b1111; // Invalid decode
        
         
         endcase // casex(xfer_bus_size)
        
       else

         n_be = 4'b1111;

       
        
     end
   
   

//----------------------------------------------------------------------
// Generate (enternal) Byte Enables.
//----------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
     begin
        
        if (~n_sys_reset)
          
           smc_n_be <= 4'hF;
        
        
        else if (smc_nextstate == `SMC_RW)
          
           smc_n_be <= n_be;
        
        else
          
           smc_n_be <= 4'hF;
        
     end
   
   
endmodule

