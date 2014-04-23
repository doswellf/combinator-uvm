//File name   : smc_ahb_lite_if.v
//Title       : 
//Created     : 1999
//Description : AMBA AHB Interface.
//            : Static Memory Controller.
//            : This block provides the AHB interface. 
//            : All AHB specific signals are contained in this
//            : block.
//            : All address decoding for the SMC module is 
//            : done in
//            : this module and chip select signals generated
//            : as well as an address valid (SMC_valid) signal
//            : back to the AHB decoder
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

//ahb interface
  module smc_ahb_lite_if  (

                      //inputs

                      hclk, 
                      n_sys_reset, 
                      haddr, 
                      hsel,
                      htrans, 
                      hwrite, 
                      hsize, 
                      hwdata,  
                      hready,  
  
                      //outputs
  
                      smc_idle,
                      read_data, 
                      mac_done, 
                      smc_done, 
                      xfer_size, 
                      n_read, 
                      new_access, 
                      addr, 
                      smc_hrdata, 
                      smc_hready,
                      smc_hresp,
                      smc_valid, 
                      cs, 
                      write_data 
                      );
  
  
//include files


//----------------------------------------------------------------------


//System I/O

  input         hclk;                   // AHB System clock
  input         n_sys_reset;            // AHB System reset (Active LOW)
 

//AHB I/O

  input  [31:0]            haddr;         // AHB Address
  input  [1:0]             htrans;        // AHB transfer type
  input                    hwrite;        // AHB read/write indication
  input  [2:0]             hsize;         // AHB transfer size
  input  [31:0]            hwdata;        // AHB write data
  input                    hready;        // AHB Muxed ready signal
  output [31:0]            smc_hrdata;    // smc read data back to AHB
                                             //  master
  output                   smc_hready;    // smc ready signal
  output [1:0]             smc_hresp;     // AHB Response signal
  output                   smc_valid;     // Ack to AHB

//other I/O
   
  input                    smc_idle;      // idle state
  input                    smc_done;      // Asserted during 
                                          // last cycle of an access
  input                    mac_done;      // End of all transfers
  input [31:0]             read_data;     // Data at internal Bus
  input               hsel;          // Chip Selects
   

  output [1:0]             xfer_size;     // Store size for MAC
  output [31:0]            addr;          // address
  output              cs;          // chip selects for external
                                              //  memories
  output [31:0]            write_data;    // Data to External Bus
  output                   n_read;        // Active low read signal 
  output                   new_access;    // New AHB valid access to
                                              //  smc detected




// Address Config







//----------------------------------------------------------------------
// Signal declarations
//----------------------------------------------------------------------

// Output register declarations

// Bus Interface

  reg  [31:0]              smc_hrdata;  // smc read data back to
                                           //  AHB master
  reg                      smc_hready;  // smc ready signal
  reg  [1:0]               smc_hresp;   // AHB Response signal
  reg                      smc_valid;   // Ack to AHB

// Internal register declarations

// Bus Interface

  reg                      new_access;  // New AHB valid access
                                           //  to smc detected
                                           //  cfg block
  reg  [31:0]              addr;        // Copy of address
  reg  [31:0]              write_data;  // Data to External Bus
  reg  [7:0]               int_cs;      // Chip(bank) Select Lines
  wire                cs;          // Chip(bank) Select Lines
  reg  [1:0]               xfer_size;   // Width of current transfer
  reg                      n_read;      // Active low read signal   
  reg                      r_ready;     // registered ready signal   
  reg                      r_hresp;     // Two cycle hresp on error
  reg                      mis_err;     // Misalignment
  reg                      dis_err;     // error

// End Bus Interface



//----------------------------------------------------------------------
// Beginning of main code
//----------------------------------------------------------------------

//----------------------------------------------------------------------
// valid access control - AHB Interface (AHB Specific)
//----------------------------------------------------------------------
// Generates the stobes required to start the smc state machine
// Generates all AHB responses.
//----------------------------------------------------------------------

   always @(hsize)

     begin
     
      xfer_size = hsize[1:0];

     end
   
//----------------------------------------------------------------------
//addr
//----------------------------------------------------------------------

   always @(haddr)
     
     begin
        
        addr = haddr;
        
     end
   
//----------------------------------------------------------------------
//chip select generation
//----------------------------------------------------------------------

   assign cs = ( hsel ) ;
    
//----------------------------------------------------------------------
// detect a valid access
//----------------------------------------------------------------------

   always @(cs or hready or htrans or mis_err)
     
     begin
             
       if (((htrans == `TRN_NONSEQ) | (htrans == `TRN_SEQ)) &
            (cs != 'd0) & hready & ~mis_err)
          
          begin
             
             smc_valid = 1'b1;
             
               
             new_access = 1'b1;
             
             
          end
             
       else
          
          begin
             
             smc_valid = 1'b0;
             new_access = 1'b0;
             
          end
             
     end

//----------------------------------------------------------------------
// Error detection
//----------------------------------------------------------------------

   always @(haddr or hsize or htrans or cs)
     
     begin
             
        if ((((haddr[0] != 1'd0) & (hsize == `SZ_HALF))      |
             ((haddr[1:0] != 2'd0) & (hsize == `SZ_WORD)))    &
            ((htrans == `TRN_NONSEQ) | (htrans == `TRN_SEQ)) &
            (cs != 1'b0) )
          
           mis_err = 1'h1;
             
        else
          
           mis_err = 1'h0;

     end 
   
//----------------------------------------------------------------------
// Disable detection
//----------------------------------------------------------------------

   always @(htrans or cs or smc_idle or hready)
     
     begin
             
           dis_err = 1'h0;
             
     end 
   
//----------------------------------------------------------------------
// Response
//----------------------------------------------------------------------

   always @(posedge hclk or negedge n_sys_reset)
     
     begin
             
        if (~n_sys_reset)
          
            begin
             
               smc_hresp <= `RSP_OKAY;
               r_hresp <= 1'd0;
             
            end
             
        else if (mis_err | dis_err)
          
            begin
             
               r_hresp <= 1'd1;
               smc_hresp <= `RSP_ERROR;
             
            end
             
        else if (r_hresp == 1'd1)
          
           begin
             
              smc_hresp <= `RSP_ERROR;
              r_hresp <= 1'd0;
             
           end
             
        else
          
           begin
             
              smc_hresp <= `RSP_OKAY;
              r_hresp <= 1'd0;
             
           end
             
     end
   
//----------------------------------------------------------------------
// assign read access sense
//----------------------------------------------------------------------

   always @(hwrite)
     
     begin
             
        n_read = hwrite;
             
     end

//----------------------------------------------------------------------
// AHB ready signal
//----------------------------------------------------------------------

   always @(posedge hclk or negedge n_sys_reset)
     
     begin
             
        if (~n_sys_reset)
          
           r_ready <= 1'b1;
             
        else if ((((htrans == `TRN_IDLE) | (htrans == `TRN_BUSY)) & 
                  (cs != 1'b0) & hready & ~mis_err & 
                  ~dis_err) | r_hresp | (hsel == 1'b0) )
          
           r_ready <= 1'b1;
             
        else
          
           r_ready <= 1'b0;
             
     end
 
//----------------------------------------------------------------------
//smc ready
//----------------------------------------------------------------------

   always @(r_ready or smc_done or mac_done)
     
     begin
             
        smc_hready = r_ready | (smc_done & mac_done);
             
     end
   
//----------------------------------------------------------------------
//read data
//----------------------------------------------------------------------
   
   always @(read_data)
     
      smc_hrdata = read_data;

//----------------------------------------------------------------------
//write data
//----------------------------------------------------------------------

   always @(hwdata)
     
      write_data = hwdata;
   


endmodule

