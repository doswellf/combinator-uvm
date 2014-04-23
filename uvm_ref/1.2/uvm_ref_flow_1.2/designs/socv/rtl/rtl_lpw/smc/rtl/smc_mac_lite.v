//File name   : smc_mac_lite.v
//Title       : 
//Created     : 1999
//Description : Multiple access controller.
//            : Static Memory Controller.
//            : The Multiple Access Control Block keeps trace of the
//            : number of accesses required to fulfill the
//            : requirements of the AHB transfer. The data is
//            : registered when multiple reads are required. The AHB
//            : holds the data during multiple writes.
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

module smc_mac_lite     (

                    //inputs
                    
                    sys_clk,
                    n_sys_reset,
                    valid_access,
                    xfer_size,
                    smc_done,
                    data_smc,
                    write_data,
                    smc_nextstate,
                    latch_data,
                    
                    //outputs
                    
                    r_num_access,
                    mac_done,
                    v_bus_size,
                    v_xfer_size,
                    read_data,
                    smc_data);
   
   
   
 


// State Machine// I/O

  input                sys_clk;        // System clock
  input                n_sys_reset;    // System reset (Active LOW)
  input                valid_access;   // Address cycle of new transfer
  input  [1:0]         xfer_size;      // xfer size, valid with valid_access
  input                smc_done;       // End of transfer
  input  [31:0]        data_smc;       // External read data
  input  [31:0]        write_data;     // Data from internal bus 
  input  [4:0]         smc_nextstate;  // State Machine  
  input                latch_data;     //latch_data is used by the MAC block    
  
  output [1:0]         r_num_access;   // Access counter
  output               mac_done;       // End of all transfers
  output [1:0]         v_bus_size;     // Registered sizes for subsequent
  output [1:0]         v_xfer_size;    // transfers in MAC transfer
  output [31:0]        read_data;      // Data to internal bus
  output [31:0]        smc_data;       // Data to external bus
  

// Output register declarations

  reg                  mac_done;       // Indicates last cycle of last access
  reg [1:0]            r_num_access;   // Access counter
  reg [1:0]            num_accesses;   //number of access
  reg [1:0]            r_xfer_size;    // Store size for MAC 
  reg [1:0]            r_bus_size;     // Store size for MAC
  reg [31:0]           read_data;      // Data path to bus IF
  reg [31:0]           r_read_data;    // Internal data store
  reg [31:0]           smc_data;


// Internal Signals

  reg [1:0]            v_bus_size;
  reg [1:0]            v_xfer_size;
  wire [4:0]           smc_nextstate;    //specifies next state
  wire [4:0]           xfer_bus_ldata;  //concatenation of xfer_size
                                         // and latch_data  
  wire [3:0]           bus_size_num_access; //concatenation of 
                                              // r_num_access
  wire [5:0]           wt_ldata_naccs_bsiz;  //concatenation of 
                                            //latch_data,r_num_access
 
   


// Main Code

//----------------------------------------------------------------------------
// Store transfer size
//----------------------------------------------------------------------------

  always @(posedge sys_clk or negedge n_sys_reset)
  
    begin
       
       if (~n_sys_reset)
         
          r_xfer_size <= 2'b00;
       
       
       else if (valid_access)
         
          r_xfer_size <= xfer_size;
       
       else
         
          r_xfer_size <= r_xfer_size;
       
    end

//--------------------------------------------------------------------
// Store bus size generation
//--------------------------------------------------------------------
  
  always @(posedge sys_clk or negedge n_sys_reset)
    
    begin
       
       if (~n_sys_reset)
         
          r_bus_size <= 2'b00;
       
       
       else if (valid_access)
         
          r_bus_size <= 2'b00;
       
       else
         
          r_bus_size <= r_bus_size;
       
    end
   

//--------------------------------------------------------------------
// Validate sizes generation
//--------------------------------------------------------------------

  always @(valid_access or r_bus_size )

    begin
       
       if (valid_access)
         
          v_bus_size = 2'b0;
       
       else
         
          v_bus_size = r_bus_size;
       
    end

//----------------------------------------------------------------------------
//v_xfer_size generation
//----------------------------------------------------------------------------   

  always @(valid_access or r_xfer_size or xfer_size)

    begin
       
       if (valid_access)
         
          v_xfer_size = xfer_size;
       
       else
         
          v_xfer_size = r_xfer_size;
       
    end
   
  

//----------------------------------------------------------------------------
// Access size decisions
// Determines the number of accesses required to build up full size
//----------------------------------------------------------------------------
   
  always @( xfer_size)
  
    begin
       
       if ((xfer_size[1:0] == `XSIZ_16))
         
          num_accesses = 2'h1; // Two accesses
       
       else if ( (xfer_size[1:0] == `XSIZ_32))
         
          num_accesses = 2'h3; // Four accesses
       
       else
         
          num_accesses = 2'h0; // One access
       
    end
   
   
   
//--------------------------------------------------------------------
// Keep track of the current access number
//--------------------------------------------------------------------
   
  always @(posedge sys_clk or negedge n_sys_reset)
  
    begin
       
       if (~n_sys_reset)
         
          r_num_access <= 2'b00;
       
       else if (valid_access)
         
          r_num_access <= num_accesses;
       
       else if (smc_done & (smc_nextstate != `SMC_STORE)  &
                      (smc_nextstate != `SMC_IDLE)   )
         
          r_num_access <= r_num_access - 2'd1;
       
       else
         
          r_num_access <= r_num_access;
       
    end
   
   

//--------------------------------------------------------------------
// Detect last access
//--------------------------------------------------------------------
   
   always @(r_num_access)
     
     begin
        
        if (r_num_access == 2'h0)
          
           mac_done = 1'b1;
             
        else
          
           mac_done = 1'b0;
          
     end
   
//----------------------------------------------------------------------------   
//signals concatenation used in case statement for read data logic
//----------------------------------------------------------------------------   

   assign wt_ldata_naccs_bsiz = { 1'b0, latch_data, r_num_access,
                                  r_bus_size};
 
   
//--------------------------------------------------------------------
// Store Read Data if required
//--------------------------------------------------------------------

   always @(posedge sys_clk or negedge n_sys_reset)
     
     begin
        
        if (~n_sys_reset)
          
           r_read_data <= 32'h0;
        
        else
          
          
          casex(wt_ldata_naccs_bsiz)
            
            
            {1'b1,5'bxxxxx} :
              
               r_read_data <= r_read_data;
            
            //    latch_data
            
            {1'b0,1'b1,2'h3,2'bxx}:
                             
              begin
                 
                 r_read_data[31:24] <= data_smc[7:0];
                 r_read_data[23:0] <= 24'h0;
                 
              end
            
            // r_num_access =2, v_bus_size = X
            
            {1'b0,1'b1,2'h2,2'bx}: 
              
              begin
                 
                 r_read_data[23:16] <= data_smc[7:0];
                 r_read_data[31:24] <= r_read_data[31:24];
                 r_read_data[15:0] <= 16'h0;
                 
              end
            
            // r_num_access =1, v_bus_size = `XSIZ_16
            
            {1'b0,1'b1,2'h1,`XSIZ_16}:
              
              begin
                 
                 r_read_data[15:0] <= 16'h0;
                 r_read_data[31:16] <= data_smc[15:0];
                 
              end
            
            //  r_num_access =1,v_bus_size == `XSIZ_8
            
            {1'b0,1'b1,2'h1,`XSIZ_8}:          
              
              begin
                 
                 r_read_data[15:8] <= data_smc[7:0];
                 r_read_data[31:16] <= r_read_data[31:16];
                 r_read_data[7:0] <= 8'h0;
                 
              end
            
            
            //  r_num_access = 0, v_bus_size == `XSIZ_16
            
            {1'b0,1'b1,2'h0,`XSIZ_16}:  // r_num_access =0
              
              
              begin
                 
                 r_read_data[15:0] <= data_smc[15:0];
                 r_read_data[31:16] <= r_read_data[31:16];
                 
              end
            
            //  r_num_access = 0, v_bus_size == `XSIZ_8 
            
            {1'b0,1'b1,2'h0,`XSIZ_8}:
              
              begin
                 
                 r_read_data[7:0] <= data_smc[7:0];
                 r_read_data[31:8] <= r_read_data[31:8];
                 
              end
            
            //  r_num_access = 0, v_bus_size == `XSIZ_32
            
            {1'b0,1'b1,2'h0,`XSIZ_32}:
              
               r_read_data[31:0] <= data_smc[31:0];                      
            
            default :
              
               r_read_data <= r_read_data;
            
            
          endcase // case
        
        
        
     end
   
   
//--------------------------------------------------------------------------
// signals concatenation for case statement use.
//--------------------------------------------------------------------------

   
   assign xfer_bus_ldata = {r_xfer_size,r_bus_size,latch_data};

//--------------------------------------------------------------------------
// read data
//--------------------------------------------------------------------------
                           
   always @( xfer_bus_ldata or data_smc or r_read_data )
       
     begin
        
        casex(xfer_bus_ldata)
          
          {`XSIZ_32,`BSIZ_32,1'b1} :
            
             read_data[31:0] = data_smc[31:0];
          
          {`XSIZ_32,`BSIZ_16,1'b1} :
                              
            begin
               
               read_data[31:16] = r_read_data[31:16];
               read_data[15:0]  = data_smc[15:0];
               
            end
          
          {`XSIZ_32,`BSIZ_8,1'b1} :
            
            begin
               
               read_data[31:8] = r_read_data[31:8];
               read_data[7:0]  = data_smc[7:0];
               
            end
          
          {`XSIZ_32,1'bx,1'bx,1'bx} :
            
            read_data = r_read_data;
          
          {`XSIZ_16,`BSIZ_16,1'b1} :
                        
            begin
               
               read_data[31:16] = data_smc[15:0];
               read_data[15:0] = data_smc[15:0];
               
            end
          
          {`XSIZ_16,`BSIZ_16,1'b0} :  
            
            begin
               
               read_data[31:16] = r_read_data[15:0];
               read_data[15:0] = r_read_data[15:0];
               
            end
          
          {`XSIZ_16,`BSIZ_32,1'b1} :  
            
            read_data = data_smc;
          
          {`XSIZ_16,`BSIZ_8,1'b1} : 
                        
            begin
               
               read_data[31:24] = r_read_data[15:8];
               read_data[23:16] = data_smc[7:0];
               read_data[15:8] = r_read_data[15:8];
               read_data[7:0] = data_smc[7:0];
            end
          
          {`XSIZ_16,`BSIZ_8,1'b0} : 
            
            begin
               
               read_data[31:16] = r_read_data[15:0];
               read_data[15:0] = r_read_data[15:0];
               
            end
          
          {`XSIZ_16,1'bx,1'bx,1'bx} :
            
            begin
               
               read_data[31:16] = r_read_data[31:16];
               read_data[15:0] = r_read_data[15:0];
               
            end
          
          {`XSIZ_8,`BSIZ_16,1'b1} :
            
            begin
               
               read_data[31:16] = data_smc[15:0];
               read_data[15:0] = data_smc[15:0];
               
            end
          
          {`XSIZ_8,`BSIZ_16,1'b0} :
            
            begin
               
               read_data[31:16] = r_read_data[15:0];
               read_data[15:0]  = r_read_data[15:0];
               
            end
          
          {`XSIZ_8,`BSIZ_32,1'b1} :   
            
            read_data = data_smc;
          
          {`XSIZ_8,`BSIZ_32,1'b0} :              
                        
                        read_data = r_read_data;
          
          {`XSIZ_8,`BSIZ_8,1'b1} :   
                                    
            begin
               
               read_data[31:24] = data_smc[7:0];
               read_data[23:16] = data_smc[7:0];
               read_data[15:8]  = data_smc[7:0];
               read_data[7:0]   = data_smc[7:0];
               
            end
          
          default:
            
            begin
               
               read_data[31:24] = r_read_data[7:0];
               read_data[23:16] = r_read_data[7:0];
               read_data[15:8]  = r_read_data[7:0];
               read_data[7:0]   = r_read_data[7:0];
               
            end
          
        endcase // case( xfer_bus_ldata)
        
        
     end
   
//---------------------------------------------------------------------------- 
// signal concatenation for use in case statement
//----------------------------------------------------------------------------
   
   assign bus_size_num_access = { r_bus_size, r_num_access};
   
//--------------------------------------------------------------------
// Select write data
//--------------------------------------------------------------------

  always @(bus_size_num_access or write_data)
  
    begin
       
       casex(bus_size_num_access)
         
         {`BSIZ_32,1'bx,1'bx}://    (v_bus_size == `BSIZ_32)
           
           smc_data = write_data;
         
         {`BSIZ_16,2'h1}:    // r_num_access == 1
                      
           begin
              
              smc_data[31:16] = 16'h0;
              smc_data[15:0] = write_data[31:16];
              
           end 
         
         {`BSIZ_16,1'bx,1'bx}:  // (v_bus_size == `BSIZ_16)  
           
           begin
              
              smc_data[31:16] = 16'h0;
              smc_data[15:0]  = write_data[15:0];
              
           end
         
         {`BSIZ_8,2'h3}:  //  (r_num_access == 3)
           
           begin
              
              smc_data[31:8] = 24'h0;
              smc_data[7:0] = write_data[31:24];
           end
         
         {`BSIZ_8,2'h2}:  //   (r_num_access == 2)
           
           begin
              
              smc_data[31:8] = 24'h0;
              smc_data[7:0] = write_data[23:16];
              
           end
         
         {`BSIZ_8,2'h1}:  //  (r_num_access == 2)
           
           begin
              
              smc_data[31:8] = 24'h0;
              smc_data[7:0]  = write_data[15:8];
              
           end 
         
         {`BSIZ_8,2'h0}:  //  (r_num_access == 0) 
           
           begin
              
              smc_data[31:8] = 24'h0;
              smc_data[7:0] = write_data[7:0];
              
           end 
         
         default:
           
           smc_data = 32'h0;
         
       endcase // casex(bus_size_num_access)
       
       
    end
   
endmodule
