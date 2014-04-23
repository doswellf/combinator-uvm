//File name   : dma_tx_sm.v
//Title       : 
//Created     : 1999
//Description : 
//Notes       : The DMA tx state machine
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

//------------------------------------------------------------------------------
// Include Files
//------------------------------------------------------------------------------

`include   "dma_defs.v"             // DMA defines

//------------------------------------------------------------------------------
// Module Declaration
//------------------------------------------------------------------------------
// dma_tx_sm
module dma_tx_sm(
            hclk,
            n_hreset,
            //xfer_start, commented by Binata on 2 Aug. as this is not used
            //source_apb, commented by Binata on 2 Aug. as this is not used
            write_grant,
            slot_available,
            hready,
            ahb_grant,
            end_xfer,
            abort,
            target_apb,
            taddr,
            pready,
            double_clk,
            //penable, commented by Binata on 2 Aug. as this is not used
            continue_write,
            count_two,
            dma_write_state,
            next_write_state
            );

//==================
// Port declarations
//==================

  input             hclk;//ahb clock
  input             n_hreset;//ahb reset
 // input             xfer_start;
 // input             source_apb;
  input             write_grant;//write grant from arbiter
  input             slot_available;//slot available
  input             hready;//ready signal
  input             ahb_grant;
  input             end_xfer;
  input             abort;
  input             target_apb;
  //input     [31:0]  taddr;
  input             taddr;
  input             pready;
  input             double_clk;
  //input             penable;
  input             continue_write;
  input             count_two;
  output    [4:0]   dma_write_state;
  output    [4:0]   next_write_state;

//====================
// Signal declarations
//====================

  wire              hclk;
  wire              n_hreset;
//  wire              xfer_start;
//  wire              source_apb;
  wire              write_grant;
  wire              slot_available;
  wire              hready;
  wire              ahb_grant;
  wire              end_xfer;
  wire              abort;
  wire              target_apb;
  wire              taddr;
  wire              pready;
  wire              double_clk;
  //wire              penable;
  wire              continue_write;
  wire              count_two;
  reg       [4:0]   dma_write_state;
  reg       [4:0]   next_write_state;

//==========
// Main code
//==========

//---------------------------
// Write state machine control
//---------------------------

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        dma_write_state <= `idle;
    else
        dma_write_state <= next_write_state;
end

// Write state machine next state control

always @(dma_write_state  or write_grant or
         slot_available or hready or ahb_grant or end_xfer or
         abort or target_apb or taddr or pready or double_clk or
         continue_write or count_two)
begin
    next_write_state = dma_write_state;
    case (dma_write_state)
        // Only move from idle when write grant is asserted and flow is high if
        // writing to an apb peripheral.
        // Move to start state 
        `idle :
            if (write_grant)
            begin
                if (target_apb & slot_available)
                    next_write_state = `write_apb_main;
                else if (~target_apb)
                    next_write_state = `write_ahb_start;
           end
// AHB WRITE STATE MACHINE
        // The ahb_request should be raised in this state.
        // Move to start address state when grant is correctly sampled high.
        `write_ahb_start :
        begin
            if (ahb_grant & hready)
                next_write_state = `write_ahb_staddr;
            else if (abort)
                next_write_state = `write_xfer_finish;                           
        end
        // The address is output in this state, if the grant is maintained
        // a second access is performed and the state moves into addrdata
        // - should only occur if a byte write followed by a half word write
        // is required.  
        `write_ahb_staddr :
        begin
            if (hready)
            begin
                next_write_state = `write_ahb_stdata;
            end
        end
        // This state enables the data to be output.Move into the handover 
        // state when hready is sampled high.If two writes are required 
        // before the next read i.e. the target address would need to start
        // with an offset of 1, then move directly into the main state
        `write_ahb_stdata :
        begin
            if (hready)
            begin
                //if (taddr[1] | continue_write)
                if (taddr | continue_write)
                    next_write_state = `write_ahb_main;
                else
                    next_write_state = `read_handover;
            end
        end
        // This state ensures the read state machine starts its next access 
        // continuing.  Write_grant is used to monitor the read state, only
        // asserted when read state machine is in wait_for_write state.
        // if an abort is issued or end_xfer move to finish_state - assumes
        // an abort will allow the current read/write cycle to complete...
        `read_handover :
        begin
            if (abort | end_xfer)
                next_write_state = `write_xfer_finish;
            else if (~write_grant)
                next_write_state = `wait_for_read;
        end
        // This state waits for the write_grant before continuing with an 
        // access.  Could recheck target_apb at this point???!?!?!?
        `wait_for_read :
        begin
            if (abort | end_xfer)
                next_write_state = `write_xfer_finish;
            else if (write_grant)
            begin
                if (target_apb & slot_available)
                    next_write_state = `write_apb_main;
                else if (~target_apb)
                    next_write_state = `write_ahb_main;
            end
        end
        // The ahb_request is raised.
        // When the ahb_grant is correctly sampled high move into
        // the address state
        `write_ahb_main :
        begin
            if (ahb_grant & hready)
                next_write_state = `write_ahb_addr;            
            else if (abort)
                next_write_state = `write_xfer_finish;                           
        end 
        // Move onto the data state when the grant is correctly sampled low.
        // each time it is sampled high start a new access - each time 
        // decrementing the burst counter (buffer pointer?) and the size.
        `write_ahb_addr :
        begin
            if (hready)
            begin
                next_write_state = `write_ahb_data;
            end
        end
        // Only stay in this state until the last data is written - move on
        // when hready is sampled high. If for some reason the grant was
        // unexpectedly removed then burst_count will not have been cleared
        // in this case return to write_ahb_main
        // One special case which needs to be covered is when the target is in
        // APB space and the final access is a 3 byte transfer - this is split
        // into a half word and a byte access but we have to ensure control
        // is not handed back to the read process between these two writes
        `write_ahb_data :
        begin
            if (hready)
            begin
                if (continue_write & ~(end_xfer | abort))
                    next_write_state = `write_ahb_main;
                else
                    next_write_state = `read_handover;
            end
        end

// APB WRITE STATE MACHINE
        // if here a read has taken place and there is enough data to be able 
        // to write a full word 
        // In this state the address and data etc. is setup and the request is
        // raised.  Once pready is received we can move to the enable state.
        // Do not have to worry about multiple writes as the only reason 
        // we would be held is if the arm is currently accessing the apb or
        // the specified slave is busy.
        // Can just look for penable as the only situation where it occurs 
        // in this state is when double_clk is asserted
        `write_apb_main :
        begin
            if (abort)
                next_write_state = `write_xfer_finish;                           
            else if (pready & (~double_clk | count_two))
                next_write_state = `write_apb_data;
        end
        // in this state the penable is asserted and the data is sampled.
        // The next state will either be write_apb_main (if another access
        // can be performed) read_handover (if the write is complete)
        `write_apb_data :
        begin
            if (abort)
                next_write_state = `write_xfer_finish;  
            else// if (pready)
            begin
                if (~double_clk | count_two)
                begin
                    if (continue_write & ~(end_xfer))
                    begin
                        next_write_state = `write_apb_main;
                    end
                    else
                        next_write_state = `read_handover;
                end
            end
        end
        `write_xfer_finish :
        begin
            next_write_state = `idle;
        end
        default :
            next_write_state = `idle;
    endcase
end

endmodule
