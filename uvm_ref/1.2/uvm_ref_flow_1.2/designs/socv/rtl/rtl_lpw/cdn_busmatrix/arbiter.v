//File name   : arbiter.v
//Title       : 
//Created     : 1999
//Description : This module arbitrates between requests coming from several Slave 
//              interfaces to use a particular Master interface and generates a grant
//              to that particular slave interface.
//              It uses a Fixed priority scheme with Request from Slave0 having the Highest priority.
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

module arbiter (

  // input ports
  hclk,
  hresetn,
  req,
  hreadyout,

  // output ports
  gnt
);

`include "bm_defs.v"

input hclk;
input hresetn;
input  [`NUM_OF_SLAVES - 1 : 0]  req;
input hreadyout;  // This is HREADYOUT input from target AHB slave.
output [`NUM_OF_SLAVES - 1 : 0]  gnt;


reg  [`NUM_OF_SLAVES - 1 : 0] status;
wire [`NUM_OF_SLAVES - 1 : 0] gnt;

wire busy;
genvar i;

// If any of the status bit is high, Master interface is busy.
assign     busy = |( status);

assign gnt = status;


// Number of status bits are equal to number of slave interfaces configured
// Any of the bit high in status signal indicates that master interface is
// serving to corresponding slave interface.

// status signal is passed as gnt to slave interfaces.
// To set any particular status bit, arbiter first checks if master interface
// is already busy, if not, and no other higher priority request exist it 
// will set status bit

// New transaction will be presented to master interface only if the AHB slave 
// attached to Master interface is ready (as indicated by hreadyout) to accept
// new transaction.
always @ (posedge hclk or negedge hresetn)
  if (~hresetn)
    status[0] <= 1'b0;
  else if (~busy & req[0] & hreadyout)
    status[0] <= 1'b1;
  else if (~req[0])
    status[0] <= 1'b0;
  else 
    status[0] <= status[0];



generate

for ( i = 1; i<= `NUM_OF_SLAVES - 1; i = i + 1)
begin

  always @ (posedge hclk or negedge hresetn)
       if (~hresetn)
         status[i] <= 1'b0;
       else if (~busy & req[i] & ~|req[i - 1 : 0 ] & hreadyout)
         status[i] <= 1'b1;
       else if (~req[i])
         status[i] <= 1'b0;
       else status[i] <= status[i];

end
endgenerate 
         
endmodule   
