//File name   : dma_rx_sm.v
//Title       : 
//Created     : 1999
//Description : 
//Notes       : The DMA rx state machine
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
// 
module dma_rx_sm(
            hclk,
            n_hreset,
            xfer_start,
            source_apb,
            word_available,
            data_available,
            hready,
            ahb_grant,
            write_complete,
            end_xfer,
            abort,
            //snoinc_buff,
            pready,
            double_clk,
            count_two,
            //target_apb,
            //saddr,
            //less_word,
            //penable,
            continue_read,
            //data_count,
            less_dble,
            //xfer_size,
            dma_read_state,
            next_read_state
            );

//==================
// Port declarations
//==================

  input             hclk;
  input             n_hreset;
  input             xfer_start;
  input             source_apb;
  input             word_available;
  input             data_available;
  input             hready;
  input             ahb_grant;
  input             write_complete;
  input             end_xfer;
  input             abort;
  //input             snoinc_buff;
  input             pready;
  input             double_clk;
  input             count_two;
  //input             target_apb;
  //input     [31:0]  saddr;
  //input             less_word;
  //input             penable;
  input             continue_read;
  //input     [3:0]   data_count;
  input             less_dble;
  //input     [15:0]  xfer_size;
  output    [4:0]   dma_read_state;
  output    [4:0]   next_read_state;

//====================
// Signal declarations
//====================

  wire              hclk;
  wire              n_hreset;
  wire              xfer_start;
  wire              source_apb;
  wire              word_available;
  wire              data_available;
  wire              hready;
  wire              ahb_grant;
  wire              write_complete;
  wire              end_xfer;
  wire              abort;
  //wire              snoinc_buff;
  wire              pready;
  wire              double_clk;
  wire              count_two;
  //wire              target_apb;
  //wire      [31:0]  saddr;
  //wire              less_word;
  //wire              penable;
  wire              continue_read;
  //wire      [3:0]   data_count;
  wire              less_dble;
  //wire      [15:0]  xfer_size;
  reg       [4:0]   dma_read_state;
  reg       [4:0]   next_read_state;



//==========
// Main code
//==========

//---------------------------
// Read state machine control
//---------------------------

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
        dma_read_state <= `idle;
    else
        dma_read_state <= next_read_state;
end

// Read state machine next state control

always @(xfer_start or source_apb or dma_read_state or word_available or 
        data_available or hready or ahb_grant or write_complete or end_xfer or
        abort or pready or double_clk or count_two or
        continue_read or less_dble )
begin
    next_read_state = dma_read_state;
    case (dma_read_state)
        // Only move out of idle state if xfer_start is asserted and 
        // at least four bytes are present if in apb space
        `idle :
        begin
            if (xfer_start)
            begin
                if (source_apb & word_available)
                    next_read_state = `read_apb_main;
                else if (~source_apb)
                    next_read_state = `read_ahb_main;
//                begin
//                    if (!residue_mode)
//                        next_read_state = `read_ahb_main;
//                    else if (residue_mode)
//                        next_read_state = `read_ahb_start;
//                end
            end
        end
// AHB READ STATE MACHINE
        // The read state machine will stay in this state until either the 
        // write_complete flag is raised or the end_xfer flag is asserted
        // Could recheck source apb at this point???!?!?!?
        `wait_for_write :
        begin
            if (end_xfer | abort)
                next_read_state = `xfer_finish;
            else if (write_complete)
            begin
                if (source_apb)
                begin
// markrn 9/3/01 mod to fix uart flow control bug - if less_dble & data_available
// continue - all access at this point are byte wide
//                    if (word_available | (less_word & data_available))
                    if (word_available | (less_dble & data_available))
                        next_read_state = `read_apb_main;
                end
                else
                    next_read_state = `read_ahb_main;
            end
        end
        // The request line is asserted in this state and burst (if possible)
        // Move into the main address state when the grant is correctly sampled
        // high.
        `read_ahb_main :
        begin
            if (ahb_grant & hready)
                next_read_state = `read_ahb_addr;
            else if (abort)
                next_read_state = `xfer_finish;                           
        end
        // Stay in this state until the grant is correctly sampled low.
        `read_ahb_addr :
        begin
            if (hready)
                next_read_state = `read_ahb_data;
        end
        // this state is held until hready is sampled high
        `read_ahb_data :
        begin
            if (hready)
            begin
                if (continue_read & ~(end_xfer | abort))
                    next_read_state = `read_ahb_main;
                else
                    next_read_state = `wait_for_write;
            end
        end

// APB_READ_STATE_MACHINE
// When accesses apb need to use buffer control.  If more than three bytes left 
// to read alwasy wait for the word available before starting an access otherwise
// use the byte_available.  Except for the fixed buffer case the read address can
// have a byte offset therefore it may be necessary to read more than four bytes
// initially, as for the ahb the following accesses are always the same length
// except for final block.
        // This state will move either into the main state for an access or to
        // the handover state if the size hits zero (need to compare read_pntr
        // to the size to generate handover signal)
        // This state is also used when flow control signals no data during
        // the final accesses and is held until data is available or an abort
        `read_apb_hold :
        begin
            if (abort)
                next_read_state = `xfer_finish;                           
            else if (continue_read)
            begin
                if (data_available)
                    next_read_state = `read_apb_main;
            end
            else
                next_read_state = `apb_data_transfer;             
        end
        // If in this state data is available
        // Only move from this state if pready is asserted or an abort occurs.
        // can just use count_two to move into data state as it is only
        // asserted in this state when double_clk is asserted
        `read_apb_main :
        begin
            if (abort)
                next_read_state = `xfer_finish;                           
            else if (pready & (~double_clk | count_two))
                next_read_state = `read_apb_data;
        end
        // Read the data and move on if pready asserted - can also be aborted
        // if continue flag is set then return to read_apb_main otherwise move
        // to handover state.  Continue flag is used to ensure enough accesses
        // are performed to accumulate a full word (normally two accesses - can
        // be four)
        // If less than four bytes remain a hold state is inserted between each
        // access to give time to stop after last byte (needed when fifo used)
        // if double_clk use hold state to ensure enable is sent low
        `read_apb_data :
        begin
            if (abort)
                next_read_state = `xfer_finish;  
            else //if (pready)
            begin
                if (~double_clk | count_two)
                begin
                    if (continue_read)
                    begin
// markrn 09/03/01 fix for uart flow control
//                        if (less_word)
                        if (less_dble)
                            next_read_state = `read_apb_hold;
                        else
                            next_read_state = `read_apb_main;
                    end
                    else
                        next_read_state = `apb_data_transfer;
                end
            end
        end
        // An extra state is required at the end of each apb read block to  
        // ensure the read data can be transferred into  the buffers before 
        // the write access attempts to read it.
        `apb_data_transfer :
        begin
            next_read_state = `wait_for_write;
        end
// TRANSFER FINISH/ABORT state 
        // raise flags to indicate type of finish
        `xfer_finish :
        begin
            next_read_state = `idle;
        end            
        default :
            next_read_state = `idle;
    endcase
end

endmodule
