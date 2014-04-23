//File name   : alut_reg_bank.v
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

// compiler directives
`include "alut_defines.v"


module alut_reg_bank
(   
   // Inputs
   pclk,
   n_p_reset,
   psel,            
   penable,       
   pwrite,         
   paddr,           
   pwdata,          

   curr_time,
   add_check_active,
   age_check_active,
   inval_in_prog,
   reused,
   d_port,
   lst_inv_addr_nrm,
   lst_inv_port_nrm,
   lst_inv_addr_cmd,
   lst_inv_port_cmd,

   // Outputs
   mac_addr,    
   d_addr,   
   s_addr,    
   s_port,    
   best_bfr_age,
   div_clk,     
   command, 
   prdata,  
   clear_reused           
);


   // APB Inputs
   input                 pclk;             // APB clock
   input                 n_p_reset;        // Reset
   input                 psel;             // Module select signal
   input                 penable;          // Enable signal 
   input                 pwrite;           // Write when HIGH and read when LOW
   input [6:0]           paddr;            // Address bus for read write
   input [31:0]          pwdata;           // APB write bus

   // Inputs from other ALUT blocks
   input [31:0]          curr_time;        // current time
   input                 add_check_active; // used to calculate status[0]
   input                 age_check_active; // used to calculate status[0]
   input                 inval_in_prog;    // status[1]
   input                 reused;           // status[2]
   input [4:0]           d_port;           // calculated destination port for tx
   input [47:0]          lst_inv_addr_nrm; // last invalidated addr normal op
   input [1:0]           lst_inv_port_nrm; // last invalidated port normal op
   input [47:0]          lst_inv_addr_cmd; // last invalidated addr via cmd
   input [1:0]           lst_inv_port_cmd; // last invalidated port via cmd
   

   output [47:0]         mac_addr;         // address of the switch
   output [47:0]         d_addr;           // address of frame to be checked
   output [47:0]         s_addr;           // address of frame to be stored
   output [1:0]          s_port;           // source port of current frame
   output [31:0]         best_bfr_age;     // best before age
   output [7:0]          div_clk;          // programmed clock divider value
   output [1:0]          command;          // command bus
   output [31:0]         prdata;           // APB read bus
   output                clear_reused;     // indicates status reg read 

   reg    [31:0]         prdata;           //APB read bus   
   reg    [31:0]         frm_d_addr_l;     
   reg    [15:0]         frm_d_addr_u;     
   reg    [31:0]         frm_s_addr_l;     
   reg    [15:0]         frm_s_addr_u;     
   reg    [1:0]          s_port;           
   reg    [31:0]         mac_addr_l;       
   reg    [15:0]         mac_addr_u;       
   reg    [31:0]         best_bfr_age;     
   reg    [7:0]          div_clk;          
   reg    [1:0]          command;          
   reg    [31:0]         lst_inv_addr_l;   
   reg    [15:0]         lst_inv_addr_u;   
   reg    [1:0]          lst_inv_port;     


   // Internal Signal Declarations
   wire                  read_enable;      //APB read enable
   wire                  write_enable;     //APB write enable
   wire   [47:0]         mac_addr;        
   wire   [47:0]         d_addr;          
   wire   [47:0]         src_addr;        
   wire                  clear_reused;    
   wire                  active;

   // ----------------------------
   // General Assignments
   // ----------------------------

   assign read_enable    = (psel & ~penable & ~pwrite);
   assign write_enable   = (psel & penable & pwrite);

   assign mac_addr  = {mac_addr_u, mac_addr_l}; 
   assign d_addr =    {frm_d_addr_u, frm_d_addr_l};
   assign s_addr    = {frm_s_addr_u, frm_s_addr_l}; 

   assign clear_reused = read_enable & (paddr == `AL_STATUS) & ~active;

   assign active = (add_check_active | age_check_active);

// ------------------------------------------------------------------------
//   Read Mux Control Block
// ------------------------------------------------------------------------

   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         prdata <= 32'h0000_0000;
      else if (read_enable)
         begin
         case (paddr)
            `AL_FRM_D_ADDR_L   : prdata <= frm_d_addr_l;
            `AL_FRM_D_ADDR_U   : prdata <= {16'd0, frm_d_addr_u};    
            `AL_FRM_S_ADDR_L   : prdata <= frm_s_addr_l; 
            `AL_FRM_S_ADDR_U   : prdata <= {16'd0, frm_s_addr_u}; 
            `AL_S_PORT         : prdata <= {30'd0, s_port}; 
            `AL_D_PORT         : prdata <= {27'd0, d_port}; 
            `AL_MAC_ADDR_L     : prdata <= mac_addr_l;
            `AL_MAC_ADDR_U     : prdata <= {16'd0, mac_addr_u};   
            `AL_CUR_TIME       : prdata <= curr_time; 
            `AL_BB_AGE         : prdata <= best_bfr_age;
            `AL_DIV_CLK        : prdata <= {24'd0, div_clk}; 
            `AL_STATUS         : prdata <= {29'd0, reused, inval_in_prog,
                                           active};
            `AL_LST_INV_ADDR_L : prdata <= lst_inv_addr_l; 
            `AL_LST_INV_ADDR_U : prdata <= {16'd0, lst_inv_addr_u};
            `AL_LST_INV_PORT   : prdata <= {30'd0, lst_inv_port};

            default:   prdata <= 32'h0000_0000;
         endcase
         end
      else
         prdata <= 32'h0000_0000;
      end 



// ------------------------------------------------------------------------
//   APB writable registers
// ------------------------------------------------------------------------
// Lower destination frame address register  
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         frm_d_addr_l <= 32'h0000_0000;         
      else if (write_enable & (paddr == `AL_FRM_D_ADDR_L))
         frm_d_addr_l <= pwdata;
      else
         frm_d_addr_l <= frm_d_addr_l;
      end   


// Upper destination frame address register  
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         frm_d_addr_u <= 16'h0000;         
      else if (write_enable & (paddr == `AL_FRM_D_ADDR_U))
         frm_d_addr_u <= pwdata[15:0];
      else
         frm_d_addr_u <= frm_d_addr_u;
      end   


// Lower source frame address register  
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         frm_s_addr_l <= 32'h0000_0000;         
      else if (write_enable & (paddr == `AL_FRM_S_ADDR_L))
         frm_s_addr_l <= pwdata;
      else
         frm_s_addr_l <= frm_s_addr_l;
      end   


// Upper source frame address register  
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         frm_s_addr_u <= 16'h0000;         
      else if (write_enable & (paddr == `AL_FRM_S_ADDR_U))
         frm_s_addr_u <= pwdata[15:0];
      else
         frm_s_addr_u <= frm_s_addr_u;
      end   


// Source port  
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         s_port <= 2'b00;         
      else if (write_enable & (paddr == `AL_S_PORT))
         s_port <= pwdata[1:0];
      else
         s_port <= s_port;
      end   


// Lower switch MAC address
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         mac_addr_l <= 32'h0000_0000;         
      else if (write_enable & (paddr == `AL_MAC_ADDR_L))
         mac_addr_l <= pwdata;
      else
         mac_addr_l <= mac_addr_l;
      end   


// Upper switch MAC address 
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         mac_addr_u <= 16'h0000;         
      else if (write_enable & (paddr == `AL_MAC_ADDR_U))
         mac_addr_u <= pwdata[15:0];
      else
         mac_addr_u <= mac_addr_u;
      end   


// Best before age 
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         best_bfr_age <= 32'hffff_ffff;         
      else if (write_enable & (paddr == `AL_BB_AGE))
         best_bfr_age <= pwdata;
      else
         best_bfr_age <= best_bfr_age;
      end   


// clock divider
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         div_clk <= 8'h00;         
      else if (write_enable & (paddr == `AL_DIV_CLK))
         div_clk <= pwdata[7:0];
      else
         div_clk <= div_clk;
      end   


// command.  Needs to be automatically cleared on following cycle
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
         command <= 2'b00; 
      else if (command != 2'b00)
         command <= 2'b00; 
      else if (write_enable & (paddr == `AL_COMMAND))
         command <= pwdata[1:0];
      else
         command <= command;
      end   


// ------------------------------------------------------------------------
//   Last invalidated port and address values.  These can either be updated
//   by normal operation of address checker overwriting existing values or
//   by the age checker being commanded to invalidate out of date values.
// ------------------------------------------------------------------------
   always @ (posedge pclk or negedge n_p_reset)
      begin 
      if (~n_p_reset)
      begin
         lst_inv_addr_l <= 32'd0;
         lst_inv_addr_u <= 16'd0;
         lst_inv_port   <= 2'd0;
      end
      else if (reused)        // reused flag from address checker
      begin
         lst_inv_addr_l <= lst_inv_addr_nrm[31:0];
         lst_inv_addr_u <= lst_inv_addr_nrm[47:32];
         lst_inv_port   <= lst_inv_port_nrm;
      end
//      else if (command == 2'b01)  // invalidate aged from age checker
      else if (inval_in_prog)  // invalidate aged from age checker
      begin
         lst_inv_addr_l <= lst_inv_addr_cmd[31:0];
         lst_inv_addr_u <= lst_inv_addr_cmd[47:32];
         lst_inv_port   <= lst_inv_port_cmd;
      end
      else
      begin
         lst_inv_addr_l <= lst_inv_addr_l;
         lst_inv_addr_u <= lst_inv_addr_u;
         lst_inv_port   <= lst_inv_port;
      end
      end
 


`ifdef ABV_ON

defparam i_apb_monitor.ABUS_WIDTH = 7;

// APB ASSERTION VIP
apb_monitor i_apb_monitor(.pclk_i(pclk), 
                          .presetn_i(n_p_reset),
                          .penable_i(penable),
                          .psel_i(psel),
                          .paddr_i(paddr),
                          .pwrite_i(pwrite),
                          .pwdata_i(pwdata),
                          .prdata_i(prdata)); 

// psl default clock = (posedge pclk);

// ASSUMPTIONS
//// active (set by address checker) and invalidation in progress should never both be set
//// psl assume_never_active_inval_aged : assume never (active & inval_in_prog);


// ASSERTION CHECKS
// never read and write at the same time
// psl assert_never_rd_wr : assert never (read_enable & write_enable);

// check apb writes, pick command reqister as arbitary example
// psl assert_cmd_wr : assert always ((paddr == `AL_COMMAND) & write_enable) -> 
//                                    next(command == prev(pwdata[1:0])) abort(~n_p_reset);


// check rw writes, pick clock divider reqister as arbitary example.  It takes 2 cycles to write
// then read back data, therefore need to store original write data for use in assertion check
reg [31:0] pwdata_d;  // 1 cycle delayed 
always @ (posedge pclk) pwdata_d <= pwdata;

// psl assert_rw_div_clk : 
// assert always {((paddr == `AL_DIV_CLK) & write_enable) ; ((paddr == `AL_DIV_CLK) & read_enable)} |=>
// {prev(pwdata_d[7:0]) == prdata[7:0]};



// COVER SANITY CHECKS
// sanity read
// psl output_for_div_clk : cover {((paddr == `AL_DIV_CLK) & read_enable); prdata[7:0] == 8'h55};


`endif


endmodule 


