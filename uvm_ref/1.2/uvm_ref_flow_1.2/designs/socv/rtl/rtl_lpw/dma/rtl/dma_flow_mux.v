//File name   : dma_flow_mux.v
//Title       : 
//Created     : 1999
//Description : DMA Flow mux
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
module dma_flow_mux(
        hclk,
        n_hreset,
        write_data,
        ahb_byte,
        // flow control inputs (three possibilities in this setup)
        data_av0,
        slot_av0,
        word_av0,
        data_av1,
        slot_av1,
        word_av1,
        data_av2,
        slot_av2,
        word_av2,
`ifdef one_channel
`else
        dma_flow_ch1,
        ch1_flow_sel,
        // outputs
        ch1_data_av,
        ch1_slot_av,
        ch1_word_av,
`ifdef two_channel
`else
        dma_flow_ch2,
        ch2_flow_sel,
        // outputs
        ch2_data_av,
        ch2_slot_av,
        ch2_word_av,
`ifdef three_channel
`else
        dma_flow_ch3,
        ch3_flow_sel,
        // outputs
        ch3_data_av,
        ch3_slot_av,
        ch3_word_av,
`endif
`endif
`endif
        dma_flow_ch0,
        ch0_flow_sel,
        // outputs
        ch0_data_av,
        ch0_slot_av,
        ch0_word_av
        );

//==================
// Port declarations
//==================

  input         hclk;
  input         n_hreset;
  input  [31:0] write_data;
  input   [3:0] ahb_byte;
  input         data_av0;
  input         slot_av0;
  input         word_av0;
  input         data_av1;
  input         slot_av1;
  input         word_av1;
  input         data_av2;
  input         slot_av2;
  input         word_av2;
  output [31:0] dma_flow_ch0;
  input         ch0_flow_sel;
  output        ch0_data_av;
  output        ch0_slot_av;
  output        ch0_word_av;
`ifdef one_channel
`else
  output [31:0] dma_flow_ch1;
  input         ch1_flow_sel;
  output        ch1_data_av;
  output        ch1_slot_av;
  output        ch1_word_av;
`ifdef two_channel
`else
  output [31:0] dma_flow_ch2;
  input         ch2_flow_sel;
  output        ch2_data_av;
  output        ch2_slot_av;
  output        ch2_word_av;
`ifdef three_channel
`else
  output [31:0] dma_flow_ch3;
  input         ch3_flow_sel;
  output        ch3_data_av;
  output        ch3_slot_av;
  output        ch3_word_av;
`endif
`endif
`endif

//====================
// Signal declarations
//====================

  wire          hclk;
  wire          n_hreset;
  wire   [31:0] write_data;
  wire    [3:0] ahb_byte;
  wire          data_av0;
  wire          slot_av0;
  wire          word_av0;
  wire          data_av1;
  wire          slot_av1;
  wire          word_av1;
  wire          data_av2;
  wire          slot_av2;
  wire          word_av2;
  reg    [31:0] dma_flow_ch0;
  wire          ch0_flow_sel;
  reg           ch0_data_av;
  reg           ch0_slot_av;
  reg           ch0_word_av;
`ifdef one_channel
`else
  reg    [31:0] dma_flow_ch1;
  wire          ch1_flow_sel;
  reg           ch1_data_av;
  reg           ch1_slot_av;
  reg           ch1_word_av;
`ifdef two_channel
`else
  reg    [31:0] dma_flow_ch2;
  wire          ch2_flow_sel;
  reg           ch2_data_av;
  reg           ch2_slot_av;
  reg           ch2_word_av;
`ifdef three_channel
`else
  reg    [31:0] dma_flow_ch3;
  wire          ch3_flow_sel;
  reg           ch3_data_av;
  reg           ch3_slot_av;
  reg           ch3_word_av;
`endif
`endif
`endif


//==========
// Main code
//==========

// Flow register access - write lines are generated in the config
// block and fed into this module.  The register contents are always output 
// for reads.

always @(posedge hclk or negedge n_hreset)
begin
    if (~n_hreset)
    begin
        dma_flow_ch0 <= 32'h00000000;
`ifdef one_channel
`else
        dma_flow_ch1 <= 32'h00000000;
`ifdef two_channel
`else
        dma_flow_ch2 <= 32'h00000000;
`ifdef three_channel
`else
        dma_flow_ch3 <= 32'h00000000;
`endif
`endif
`endif
    end
    else
    begin
        // Ch0 flow control register
        if (ch0_flow_sel)
        begin
            if (ahb_byte[0])
                dma_flow_ch0[7:0] <= write_data[7:0];
            if (ahb_byte[1])
                dma_flow_ch0[15:8] <= write_data[15:8];
            if (ahb_byte[2])
                dma_flow_ch0[23:16] <= write_data[23:16];
            if (ahb_byte[3])
                dma_flow_ch0[31:24] <= write_data[31:24];
        end
`ifdef one_channel
`else
        // Ch1 flow control register
        if (ch1_flow_sel)
        begin
            if (ahb_byte[0])
                dma_flow_ch1[7:0] <= write_data[7:0];
            if (ahb_byte[1])
                dma_flow_ch1[15:8] <= write_data[15:8];
            if (ahb_byte[2])
                dma_flow_ch1[23:16] <= write_data[23:16];
            if (ahb_byte[3])
                dma_flow_ch1[31:24] <= write_data[31:24];
        end
`ifdef two_channel
`else
        // Ch2 flow control register
        if (ch2_flow_sel)
        begin
            if (ahb_byte[0])
                dma_flow_ch2[7:0] <= write_data[7:0];
            if (ahb_byte[1])
                dma_flow_ch2[15:8] <= write_data[15:8];
            if (ahb_byte[2])
                dma_flow_ch2[23:16] <= write_data[23:16];
            if (ahb_byte[3])
                dma_flow_ch2[31:24] <= write_data[31:24];
        end
`ifdef three_channel
`else
        // ch3 flow control register
        if (ch3_flow_sel)
        begin
            if (ahb_byte[0])
                dma_flow_ch3[7:0] <= write_data[7:0];
            if (ahb_byte[1])
                dma_flow_ch3[15:8] <= write_data[15:8];
            if (ahb_byte[2])
                dma_flow_ch3[23:16] <= write_data[23:16];
            if (ahb_byte[3])
                dma_flow_ch3[31:24] <= write_data[31:24];
        end
`endif
`endif
`endif
    end
end

// Separate control into separate process for each channel.
// Each channel can have one or all of the flow control lines connected
// always assume the last set of flow control inputs is tied active.
// two bits are used for each flow control input - allows up to three
// channels

//==========
// CHANNEL 0
//==========

always @(dma_flow_ch0 or slot_av0 or slot_av1 or slot_av2)
begin
    case (dma_flow_ch0[1:0])
        `source0 :
            ch0_slot_av = slot_av0;
        `source1 :
            ch0_slot_av = slot_av1;
        `source2 :
            ch0_slot_av = slot_av2;
        default :
            ch0_slot_av = 1'b1;
    endcase
end

always @(dma_flow_ch0 or data_av0 or data_av1 or data_av2)
begin
    case (dma_flow_ch0[3:2])
        `dest0 :
            ch0_data_av = data_av0;
        `dest1 :
            ch0_data_av = data_av1;
        `dest2 :
            ch0_data_av = data_av2;
        default :
            ch0_data_av = 1'b1;
    endcase
end

always @(dma_flow_ch0 or word_av0 or word_av1 or word_av2)
begin
    case (dma_flow_ch0[5:4])
        `dest0 :
            ch0_word_av = word_av0;
        `dest1 :
            ch0_word_av = word_av1;
        `dest2 :
            ch0_word_av = word_av2;
        default :
            ch0_word_av = 1'b1;
    endcase
end

`ifdef one_channel
`else
//==========
// CHANNEL 1
//==========

always @(dma_flow_ch1 or slot_av0 or slot_av1 or slot_av2)
begin
    case (dma_flow_ch1[1:0])
        `source0 :
            ch1_slot_av = slot_av0;
        `source1 :
            ch1_slot_av = slot_av1;
        `source2 :
            ch1_slot_av = slot_av2;
        default :
            ch1_slot_av = 1'b1;
    endcase
end

always @(dma_flow_ch1 or data_av0 or data_av1 or data_av2)
begin
    case (dma_flow_ch1[3:2])
        `dest0 :
            ch1_data_av = data_av0;
        `dest1 :
            ch1_data_av = data_av1;
        `dest2 :
            ch1_data_av = data_av2;
        default :
            ch1_data_av = 1'b1;
    endcase
end

always @(dma_flow_ch1 or word_av0 or word_av1 or word_av2)
begin
    case (dma_flow_ch1[5:4])
        `dest0 :
            ch1_word_av = word_av0;
        `dest1 :
            ch1_word_av = word_av1;
        `dest2 :
            ch1_word_av = word_av2;
        default :
            ch1_word_av = 1'b1;
    endcase
end

`ifdef two_channel
`else
//==========
// CHANNEL 2
//==========

always @(dma_flow_ch2 or slot_av0 or slot_av1 or slot_av2)
begin
    case (dma_flow_ch2[1:0])
        `source0 :
            ch2_slot_av = slot_av0;
        `source1 :
            ch2_slot_av = slot_av1;
        `source2 :
            ch2_slot_av = slot_av2;
        default :
            ch2_slot_av = 1'b1;
    endcase
end

always @(dma_flow_ch2 or data_av0 or data_av1 or data_av2)
begin
    case (dma_flow_ch2[3:2])
        `dest0 :
            ch2_data_av = data_av0;
        `dest1 :
            ch2_data_av = data_av1;
        `dest2 :
            ch2_data_av = data_av2;
        default :
            ch2_data_av = 1'b1;
    endcase
end

always @(dma_flow_ch2 or word_av0 or word_av1 or word_av2)
begin
    case (dma_flow_ch2[5:4])
        `dest0 :
            ch2_word_av = word_av0;
        `dest1 :
            ch2_word_av = word_av1;
        `dest2 :
            ch2_word_av = word_av2;
        default :
            ch2_word_av = 1'b1;
    endcase
end

`ifdef three_channel
`else
//==========
// CHANNEL 3
//==========

always @(dma_flow_ch3 or slot_av0 or slot_av1 or slot_av2)
begin
    case (dma_flow_ch3[1:0])
        `source0 :
            ch3_slot_av = slot_av0;
        `source1 :
            ch3_slot_av = slot_av1;
        `source2 :
            ch3_slot_av = slot_av2;
        default :
            ch3_slot_av = 1'b1;
    endcase
end

always @(dma_flow_ch3 or data_av0 or data_av1 or data_av2)
begin
    case (dma_flow_ch3[3:2])
        `dest0 :
            ch3_data_av = data_av0;
        `dest1 :
            ch3_data_av = data_av1;
        `dest2 :
            ch3_data_av = data_av2;
        default :
            ch3_data_av = 1'b1;
    endcase
end

always @(dma_flow_ch3 or word_av0 or word_av1 or word_av2)
begin
    case (dma_flow_ch3[5:4])
        `dest0 :
            ch3_word_av = word_av0;
        `dest1 :
            ch3_word_av = word_av1;
        `dest2 :
            ch3_word_av = word_av2;
        default :
            ch3_word_av = 1'b1;
    endcase
end
`endif
`endif
`endif

endmodule
