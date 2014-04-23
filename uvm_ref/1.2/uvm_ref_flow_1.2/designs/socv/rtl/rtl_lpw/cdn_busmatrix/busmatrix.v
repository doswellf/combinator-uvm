//File name   : busmatrix.v
//Title       : 
//Created     : 1999
//Description : This is a top level for BusMatrix module. It instantiates slave_if 
//              "NUM_OF_SLAVES" times and instantiates master_if "NUM_OF_MASTERS"
//              times.
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

`include "bm_defs.v"
module BusMatrix (
      HCLK,
      HRESETn,

      REMAP,

// Slave 0  Input port

`ifdef SLAVE0
         HSELS0,
         HADDRS0,
         HTRANSS0,
         HWRITES0,
         HSIZES0,
         HBURSTS0,
         HPROTS0,
         HMASTERS0,
         HWDATAS0,
         HMASTLOCKS0,
         HREADYS0,
`endif


`ifdef SLAVE1
// Slave 1 Input port
         HSELS1,
         HADDRS1,
         HTRANSS1,
         HWRITES1,
         HSIZES1,
         HBURSTS1,
         HPROTS1,
         HMASTERS1,
         HWDATAS1,
         HMASTLOCKS1,
         HREADYS1,
`endif

`ifdef SLAVE2
// Slave 2 Input port
         HSELS2,
         HADDRS2,
         HTRANSS2,
         HWRITES2,
         HSIZES2,
         HBURSTS2,
         HPROTS2,
         HMASTERS2,
         HWDATAS2,
         HMASTLOCKS2,
         HREADYS2,
`endif

`ifdef SLAVE3
// Slave 3 Input port
         HSELS3,
         HADDRS3,
         HTRANSS3,
         HWRITES3,
         HSIZES3,
         HBURSTS3,
         HPROTS3,
         HMASTERS3,
         HWDATAS3,
         HMASTLOCKS3,
         HREADYS3,
`endif

`ifdef SLAVE4
// Slave 4 Input port
         HSELS4,
         HADDRS4,
         HTRANSS4,
         HWRITES4,
         HSIZES4,
         HBURSTS4,
         HPROTS4,
         HMASTERS4,
         HWDATAS4,
         HMASTLOCKS4,
         HREADYS4,
`endif

`ifdef SLAVE5
// Slave 5 Input port
         HSELS5,
         HADDRS5,
         HTRANSS5,
         HWRITES5,
         HSIZES5,
         HBURSTS5,
         HPROTS5,
         HMASTERS5,
         HWDATAS5,
         HMASTLOCKS5,
         HREADYS5,
`endif

`ifdef SLAVE6
// Slave 6 Input port
         HSELS6,
         HADDRS6,
         HTRANSS6,
         HWRITES6,
         HSIZES6,
         HBURSTS6,
         HPROTS6,
         HMASTERS6,
         HWDATAS6,
         HMASTLOCKS6,
         HREADYS6,
`endif

`ifdef SLAVE7
// Slave 7 Input port
         HSELS7,
         HADDRS7,
         HTRANSS7,
         HWRITES7,
         HSIZES7,
         HBURSTS7,
         HPROTS7,
         HMASTERS7,
         HWDATAS7,
         HMASTLOCKS7,
         HREADYS7,
`endif

`ifdef SLAVE8
// Slave 8 Input port
         HSELS8,
         HADDRS8,
         HTRANSS8,
         HWRITES8,
         HSIZES8,
         HBURSTS8,
         HPROTS8,
         HMASTERS8,
         HWDATAS8,
         HMASTLOCKS8,
         HREADYS8,
`endif

`ifdef SLAVE9
// Slave 9 Input port
         HSELS9,
         HADDRS9,
         HTRANSS9,
         HWRITES9,
         HSIZES9,
         HBURSTS9,
         HPROTS9,
         HMASTERS9,
         HWDATAS9,
         HMASTLOCKS9,
         HREADYS9,
`endif

`ifdef SLAVE10
// Slave 10 Input port
         HSELS10,
         HADDRS10,
         HTRANSS10,
         HWRITES10,
         HSIZES10,
         HBURSTS10,
         HPROTS10,
         HMASTERS10,
         HWDATAS10,
         HMASTLOCKS10,
         HREADYS10,
`endif

`ifdef SLAVE11
// Slave 11 Input port
         HSELS11,
         HADDRS11,
         HTRANSS11,
         HWRITES11,
         HSIZES11,
         HBURSTS11,
         HPROTS11,
         HMASTERS11,
         HWDATAS11,
         HMASTLOCKS11,
         HREADYS11,
`endif

`ifdef SLAVE12
// Slave 12 Input port
         HSELS12,
         HADDRS12,
         HTRANSS12,
         HWRITES12,
         HSIZES12,
         HBURSTS12,
         HPROTS12,
         HMASTERS12,
         HWDATAS12,
         HMASTLOCKS12,
         HREADYS12,
`endif

`ifdef SLAVE13
// Slave 13 Input port
         HSELS13,
         HADDRS13,
         HTRANSS13,
         HWRITES13,
         HSIZES13,
         HBURSTS13,
         HPROTS13,
         HMASTERS13,
         HWDATAS13,
         HMASTLOCKS13,
         HREADYS13,
`endif

`ifdef SLAVE14
// Slave 14 Input port
         HSELS14,
         HADDRS14,
         HTRANSS14,
         HWRITES14,
         HSIZES14,
         HBURSTS14,
         HPROTS14,
         HMASTERS14,
         HWDATAS14,
         HMASTLOCKS14,
         HREADYS14,
`endif

`ifdef SLAVE15
// Slave 15 Input port
         HSELS15,
         HADDRS15,
         HTRANSS15,
         HWRITES15,
         HSIZES15,
         HBURSTS15,
         HPROTS15,
         HMASTERS15,
         HWDATAS15,
         HMASTLOCKS15,
         HREADYS15,
`endif


`ifdef MASTER0
// Master 0 Input port
         HRDATAM0,
         HREADYOUTM0,
         HRESPM0,
`endif

`ifdef MASTER1
// Master 1 Input port
         HRDATAM1,
         HREADYOUTM1,
         HRESPM1,
`endif

`ifdef MASTER2
// Master 2 Input port
         HRDATAM2,
         HREADYOUTM2,
         HRESPM2,
`endif

`ifdef MASTER3
// Master 3 Input port
         HRDATAM3,
         HREADYOUTM3,
         HRESPM3,
`endif

`ifdef MASTER4
// Master 4 Input port
         HRDATAM4,
         HREADYOUTM4,
         HRESPM4,
`endif

`ifdef MASTER5
// Master 5 Input port
         HRDATAM5,
         HREADYOUTM5,
         HRESPM5,
`endif

`ifdef MASTER6
// Master 6 Input port
         HRDATAM6,
         HREADYOUTM6,
         HRESPM6,
`endif

`ifdef MASTER7
// Master 7 Input port
         HRDATAM7,
         HREADYOUTM7,
         HRESPM7,
`endif

`ifdef MASTER8
// Master 8 Input port
         HRDATAM8,
         HREADYOUTM8,
         HRESPM8,
`endif

`ifdef MASTER9
// Master 9 Input port
         HRDATAM9,
         HREADYOUTM9,
         HRESPM9,
`endif

`ifdef MASTER10
// Master 10 Input port
         HRDATAM10,
         HREADYOUTM10,
         HRESPM10,
`endif

`ifdef MASTER11
// Master 11 Input port
         HRDATAM11,
         HREADYOUTM11,
         HRESPM11,
`endif

`ifdef MASTER12
// Master 12 Input port
         HRDATAM12,
         HREADYOUTM12,
         HRESPM12,
`endif

`ifdef MASTER13
// Master 13 Input port
         HRDATAM13,
         HREADYOUTM13,
         HRESPM13,
`endif

`ifdef MASTER14
// Master 14 Input port
         HRDATAM14,
         HREADYOUTM14,
         HRESPM14,
`endif

`ifdef MASTER15
// Master 15 Input port
         HRDATAM15,
         HREADYOUTM15,
         HRESPM15,
`endif

          SCANENABLE,
          SCANINHCLK,

`ifdef MASTER0
// Master 0 Output port
          HSELM0,
          HADDRM0,
          HTRANSM0,
          HWRITEM0,
          HSIZEM0,
          HBURSTM0,
          HPROTM0,
          HMASTERM0,
          HWDATAM0,
          HMASTLOCKM0,
          HREADYMUXM0,
`endif

`ifdef MASTER1
// Master 1 Output port
          HSELM1,
          HADDRM1,
          HTRANSM1,
          HWRITEM1,
          HSIZEM1,
          HBURSTM1,
          HPROTM1,
          HMASTERM1,
          HWDATAM1,
          HMASTLOCKM1,
          HREADYMUXM1,
`endif

`ifdef MASTER2
// Master 2 Output port
          HSELM2,
          HADDRM2,
          HTRANSM2,
          HWRITEM2,
          HSIZEM2,
          HBURSTM2,
          HPROTM2,
          HMASTERM2,
          HWDATAM2,
          HMASTLOCKM2,
          HREADYMUXM2,
`endif

`ifdef MASTER3
// Master 3 Output port
          HSELM3,
          HADDRM3,
          HTRANSM3,
          HWRITEM3,
          HSIZEM3,
          HBURSTM3,
          HPROTM3,
          HMASTERM3,
          HWDATAM3,
          HMASTLOCKM3,
          HREADYMUXM3,
`endif

`ifdef MASTER4
// Master 4 Output port
          HSELM4,
          HADDRM4,
          HTRANSM4,
          HWRITEM4,
          HSIZEM4,
          HBURSTM4,
          HPROTM4,
          HMASTERM4,
          HWDATAM4,
          HMASTLOCKM4,
          HREADYMUXM4,
`endif

`ifdef MASTER5
// Master 5 Output port
          HSELM5,
          HADDRM5,
          HTRANSM5,
          HWRITEM5,
          HSIZEM5,
          HBURSTM5,
          HPROTM5,
          HMASTERM5,
          HWDATAM5,
          HMASTLOCKM5,
          HREADYMUXM5,
`endif

`ifdef MASTER6
// Master 6 Output port
          HSELM6,
          HADDRM6,
          HTRANSM6,
          HWRITEM6,
          HSIZEM6,
          HBURSTM6,
          HPROTM6,
          HMASTERM6,
          HWDATAM6,
          HMASTLOCKM6,
          HREADYMUXM6,
`endif

`ifdef MASTER7
// Master 7 Output port
          HSELM7,
          HADDRM7,
          HTRANSM7,
          HWRITEM7,
          HSIZEM7,
          HBURSTM7,
          HPROTM7,
          HMASTERM7,
          HWDATAM7,
          HMASTLOCKM7,
          HREADYMUXM7,
`endif

`ifdef MASTER8
// Master 8 Output port
          HSELM8,
          HADDRM8,
          HTRANSM8,
          HWRITEM8,
          HSIZEM8,
          HBURSTM8,
          HPROTM8,
          HMASTERM8,
          HWDATAM8,
          HMASTLOCKM8,
          HREADYMUXM8,
`endif

`ifdef MASTER9
// Master 9 Output port
          HSELM9,
          HADDRM9,
          HTRANSM9,
          HWRITEM9,
          HSIZEM9,
          HBURSTM9,
          HPROTM9,
          HMASTERM9,
          HWDATAM9,
          HMASTLOCKM9,
          HREADYMUXM9,
`endif

`ifdef MASTER10
// Master 10 Output port
          HSELM10,
          HADDRM10,
          HTRANSM10,
          HWRITEM10,
          HSIZEM10,
          HBURSTM10,
          HPROTM10,
          HMASTERM10,
          HWDATAM10,
          HMASTLOCKM10,
          HREADYMUXM10,
`endif

`ifdef MASTER11
// Master 11 Output port
          HSELM11,
          HADDRM11,
          HTRANSM11,
          HWRITEM11,
          HSIZEM11,
          HBURSTM11,
          HPROTM11,
          HMASTERM11,
          HWDATAM11,
          HMASTLOCKM11,
          HREADYMUXM11,
`endif

`ifdef MASTER12
// Master 12 Output port
          HSELM12,
          HADDRM12,
          HTRANSM12,
          HWRITEM12,
          HSIZEM12,
          HBURSTM12,
          HPROTM12,
          HMASTERM12,
          HWDATAM12,
          HMASTLOCKM12,
          HREADYMUXM12,
`endif

`ifdef MASTER13
// Master 13 Output port
          HSELM13,
          HADDRM13,
          HTRANSM13,
          HWRITEM13,
          HSIZEM13,
          HBURSTM13,
          HPROTM13,
          HMASTERM13,
          HWDATAM13,
          HMASTLOCKM13,
          HREADYMUXM13,
`endif

`ifdef MASTER14
// Master 14 Output port
          HSELM14,
          HADDRM14,
          HTRANSM14,
          HWRITEM14,
          HSIZEM14,
          HBURSTM14,
          HPROTM14,
          HMASTERM14,
          HWDATAM14,
          HMASTLOCKM14,
          HREADYMUXM14,
`endif

`ifdef MASTER15
// Master 15 Output port
          HSELM15,
          HADDRM15,
          HTRANSM15,
          HWRITEM15,
          HSIZEM15,
          HBURSTM15,
          HPROTM15,
          HMASTERM15,
          HWDATAM15,
          HMASTLOCKM15,
          HREADYMUXM15,
`endif


`ifdef SLAVE0
// Slave 0 Output port
         HRDATAS0,
         HREADYOUTS0,
         HRESPS0,
`endif

`ifdef SLAVE1
// Slave 1 Output port
         HRDATAS1,
         HREADYOUTS1,
         HRESPS1,
`endif

`ifdef SLAVE2
// Slave 2 Output port
         HRDATAS2,
         HREADYOUTS2,
         HRESPS2,
`endif

`ifdef SLAVE3
// Slave 3 Output port
         HRDATAS3,
         HREADYOUTS3,
         HRESPS3,
`endif

`ifdef SLAVE4
// Slave 4 Output port
         HRDATAS4,
         HREADYOUTS4,
         HRESPS4,
`endif

`ifdef SLAVE5
// Slave 5 Output port
         HRDATAS5,
         HREADYOUTS5,
         HRESPS5,
`endif

`ifdef SLAVE6
// Slave 6 Output port
         HRDATAS6,
         HREADYOUTS6,
         HRESPS6,
`endif

`ifdef SLAVE7
// Slave 7 Output port
         HRDATAS7,
         HREADYOUTS7,
         HRESPS7,
`endif

`ifdef SLAVE8
// Slave 8 Output port
         HRDATAS8,
         HREADYOUTS8,
         HRESPS8,
`endif

`ifdef SLAVE9
// Slave 9 Output port
         HRDATAS9,
         HREADYOUTS9,
         HRESPS9,
`endif

`ifdef SLAVE10
// Slave 10 Output port
         HRDATAS10,
         HREADYOUTS10,
         HRESPS10,
`endif

`ifdef SLAVE11
// Slave 11 Output port
         HRDATAS11,
         HREADYOUTS11,
         HRESPS11,
`endif

`ifdef SLAVE12
// Slave 12 Output port
         HRDATAS12,
         HREADYOUTS12,
         HRESPS12,
`endif

`ifdef SLAVE13
// Slave 13 Output port
         HRDATAS13,
         HREADYOUTS13,
         HRESPS13,
`endif

`ifdef SLAVE14
// Slave 14 Output port
         HRDATAS14,
         HREADYOUTS14,
         HRESPS14,
`endif

`ifdef SLAVE15
// Slave 15 Output port
         HRDATAS15,
         HREADYOUTS15,
         HRESPS15,
`endif


         SCANOUTHCLK
);

`include "bm_params.v"

input HCLK;
input HRESETn;

input REMAP;

`ifdef SLAVE0
// Slave 0 Input port
input    HSELS0;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS0;
input  [1 : 0]  HTRANSS0;
input    HWRITES0;
input [2:0]   HSIZES0;
input [2 : 0]   HBURSTS0;
input [3 : 0]   HPROTS0;
input [3 : 0]   HMASTERS0;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS0;
input    HMASTLOCKS0; 
input    HREADYS0;
`endif

`ifdef SLAVE1
// Slave 1 Input port
input    HSELS1;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS1;
input  [1 : 0]  HTRANSS1;
input    HWRITES1;
input [2:0]   HSIZES1;
input [2 : 0]   HBURSTS1;
input [3 : 0]   HPROTS1;
input [3 : 0]   HMASTERS1;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS1;
input    HMASTLOCKS1;
input    HREADYS1;
`endif

`ifdef SLAVE2
// Slave 2 Input port
input    HSELS2;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS2;
input  [1 : 0]  HTRANSS2;
input    HWRITES2;
input [2:0]   HSIZES2;
input [2 : 0]   HBURSTS2;
input [3 : 0]   HPROTS2;
input [3 : 0]   HMASTERS2;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS2;
input    HMASTLOCKS2;
input    HREADYS2;
`endif

`ifdef SLAVE3
// Slave 3 Input port
input    HSELS3;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS3;
input  [1 : 0]  HTRANSS3;
input    HWRITES3;
input [2:0]   HSIZES3;
input [2 : 0]   HBURSTS3;
input [3 : 0]   HPROTS3;
input [3 : 0]   HMASTERS3;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS3;
input    HMASTLOCKS3;
input    HREADYS3;
`endif

`ifdef SLAVE4
// Slave 4 Input port
input    HSELS4;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS4;
input  [1 : 0]  HTRANSS4;
input    HWRITES4;
input [2:0]   HSIZES4;
input [2 : 0]   HBURSTS4;
input [3 : 0]   HPROTS4;
input [3 : 0]   HMASTERS4;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS4;
input    HMASTLOCKS4;
input    HREADYS4;
`endif

`ifdef SLAVE5
// Slave 5 Input port
input    HSELS5;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS5;
input  [1 : 0]  HTRANSS5;
input    HWRITES5;
input [2:0]   HSIZES5;
input [2 : 0]   HBURSTS5;
input [3 : 0]   HPROTS5;
input [3 : 0]   HMASTERS5;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS5;
input    HMASTLOCKS5;
input    HREADYS5;
`endif

`ifdef SLAVE6
// Slave 6 Input port
input    HSELS6;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS6;
input  [1 : 0]  HTRANSS6;
input    HWRITES6;
input [2:0]   HSIZES6;
input [2 : 0]   HBURSTS6;
input [3 : 0]   HPROTS6;
input [3 : 0]   HMASTERS6;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS6;
input    HMASTLOCKS6;
input    HREADYS6;
`endif

`ifdef SLAVE7
// Slave 7 Input port
input    HSELS7;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS7;
input  [1 : 0]  HTRANSS7;
input    HWRITES7;
input [2:0]   HSIZES7;
input [2 : 0]   HBURSTS7;
input [3 : 0]   HPROTS7;
input [3 : 0]   HMASTERS7;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS7;
input    HMASTLOCKS7;
input    HREADYS7;
`endif

`ifdef SLAVE8
// Slave 8 Input port
input    HSELS8;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS8;
input  [1 : 0]  HTRANSS8;
input    HWRITES8;
input [2:0]   HSIZES8;
input [2 : 0]   HBURSTS8;
input [3 : 0]   HPROTS8;
input [3 : 0]   HMASTERS8;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS8;
input    HMASTLOCKS8;
input    HREADYS8;
`endif

`ifdef SLAVE9
// Slave 9 Input port
input    HSELS9;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS9;
input  [1 : 0]  HTRANSS9;
input    HWRITES9;
input [2:0]   HSIZES9;
input [2 : 0]   HBURSTS9;
input [3 : 0]   HPROTS9;
input [3 : 0]   HMASTERS9;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS9;
input    HMASTLOCKS9;
input    HREADYS9;
`endif

`ifdef SLAVE10
// Slave 10 Input port
input    HSELS10;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS10;
input  [1 : 0]  HTRANSS10;
input    HWRITES10;
input [2:0]   HSIZES10;
input [2 : 0]   HBURSTS10;
input [3 : 0]   HPROTS10;
input [3 : 0]   HMASTERS10;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS10;
input    HMASTLOCKS10;
input    HREADYS10;
`endif

`ifdef SLAVE11
// Slave 11 Input port
input    HSELS11;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS11;
input  [1 : 0]  HTRANSS11;
input    HWRITES11;
input [2:0]   HSIZES11;
input [2 : 0]   HBURSTS11;
input [3 : 0]   HPROTS11;
input [3 : 0]   HMASTERS11;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS11;
input    HMASTLOCKS11;
input    HREADYS11;
`endif

`ifdef SLAVE12
// Slave 12 Input port
input    HSELS12;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS12;
input  [1 : 0]  HTRANSS12;
input    HWRITES12;
input [2:0]   HSIZES12;
input [2 : 0]   HBURSTS12;
input [3 : 0]   HPROTS12;
input [3 : 0]   HMASTERS12;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS12;
input    HMASTLOCKS12;
input    HREADYS12;
`endif

`ifdef SLAVE13
// Slave 13 Input port
input    HSELS13;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS13;
input  [1 : 0]  HTRANSS13;
input    HWRITES13;
input [2:0]   HSIZES13;
input [2 : 0]   HBURSTS13;
input [3 : 0]   HPROTS13;
input [3 : 0]   HMASTERS13;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS13;
input    HMASTLOCKS13;
input    HREADYS13;
`endif

`ifdef SLAVE14
// Slave 14 Input port
input    HSELS14;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS14;
input  [1 : 0]  HTRANSS14;
input    HWRITES14;
input [2:0]   HSIZES14;
input [2 : 0]   HBURSTS14;
input [3 : 0]   HPROTS14;
input [3 : 0]   HMASTERS14;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS14;
input    HMASTLOCKS14;
input    HREADYS14;
`endif

`ifdef SLAVE15
// Slave 15 Input port
input    HSELS15;
input  [`AHB_ADDR_WIDTH - 1 : 0]  HADDRS15;
input  [1 : 0]  HTRANSS15;
input    HWRITES15;
input [2:0]   HSIZES15;
input [2 : 0]   HBURSTS15;
input [3 : 0]   HPROTS15;
input [3 : 0]   HMASTERS15;
input [`AHB_DATA_WIDTH - 1 : 0]   HWDATAS15;
input    HMASTLOCKS15;
input    HREADYS15;
`endif

`ifdef MASTER0
// Master 0 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM0;
input    HREADYOUTM0;
input [1 : 0]   HRESPM0;
`endif

`ifdef MASTER1
// Master 1 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM1;
input    HREADYOUTM1;
input [1 : 0]   HRESPM1;
`endif

`ifdef MASTER2
// Master 2 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM2;
input    HREADYOUTM2;
input [1 : 0]   HRESPM2;
`endif

`ifdef MASTER3
// Master 3 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM3;
input    HREADYOUTM3;
input [1 : 0]   HRESPM3;
`endif

`ifdef MASTER4
// Master 4 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM4;
input    HREADYOUTM4;
input [1 : 0]   HRESPM4;
`endif

`ifdef MASTER5
// Master 5 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM5;
input    HREADYOUTM5;
input [1 : 0]   HRESPM5;
`endif

`ifdef MASTER6
// Master 6 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM6;
input    HREADYOUTM6;
input [1 : 0]   HRESPM6;
`endif

`ifdef MASTER7
// Master 7 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM7;
input    HREADYOUTM7;
input [1 : 0]   HRESPM7;
`endif

`ifdef MASTER8
// Master 8 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM8;
input    HREADYOUTM8;
input [1 : 0]   HRESPM8;
`endif

`ifdef MASTER9
// Master 9 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM9;
input    HREADYOUTM9;
input [1 : 0]   HRESPM9;
`endif

`ifdef MASTER10
// Master 10 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM10;
input    HREADYOUTM10;
input [1 : 0]   HRESPM10;
`endif

`ifdef MASTER11
// Master 11 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM11;
input    HREADYOUTM11;
input [1 : 0]   HRESPM11;
`endif

`ifdef MASTER12
// Master 12 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM12;
input    HREADYOUTM12;
input [1 : 0]   HRESPM12;
`endif

`ifdef MASTER13
// Master 13 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM13;
input    HREADYOUTM13;
input [1 : 0]   HRESPM13;
`endif

`ifdef MASTER14
// Master 14 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM14;
input    HREADYOUTM14;
input [1 : 0]   HRESPM14;
`endif

`ifdef MASTER15
// Master 15 Input port
input [`AHB_DATA_WIDTH - 1 : 0]   HRDATAM15;
input    HREADYOUTM15;
input [1 : 0]   HRESPM15;
`endif

input     SCANENABLE;
input     SCANINHCLK;

`ifdef MASTER0
// Master 0 Output port
output    HSELM0;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM0;
output [1 : 0]   HTRANSM0;
output    HWRITEM0;
output [2 : 0]   HSIZEM0;
output [2 : 0]   HBURSTM0;
output [3 : 0]   HPROTM0;
output [3 : 0]   HMASTERM0;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM0;
output    HMASTLOCKM0;
output    HREADYMUXM0;
`endif

`ifdef MASTER1
// Master 1 Output port
output    HSELM1;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM1;
output [1 : 0]   HTRANSM1;
output    HWRITEM1;
output [2 : 0]   HSIZEM1;
output [2 : 0]   HBURSTM1;
output [3 : 0]   HPROTM1;
output [3 : 0]   HMASTERM1;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM1;
output    HMASTLOCKM1;
output    HREADYMUXM1;
`endif

`ifdef MASTER2
// Master 2 Output port
output    HSELM2;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM2;
output [1 : 0]   HTRANSM2;
output    HWRITEM2;
output [2 : 0]   HSIZEM2;
output [2 : 0]   HBURSTM2;
output [3 : 0]   HPROTM2;
output [3 : 0]   HMASTERM2;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM2;
output    HMASTLOCKM2;
output    HREADYMUXM2;
`endif

`ifdef MASTER3
// Master 3 Output port
output    HSELM3;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM3;
output [1 : 0]   HTRANSM3;
output    HWRITEM3;
output [2 : 0]   HSIZEM3;
output [2 : 0]   HBURSTM3;
output [3 : 0]   HPROTM3;
output [3 : 0]   HMASTERM3;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM3;
output    HMASTLOCKM3;
output    HREADYMUXM3;
`endif

`ifdef MASTER4
// Master 4 Output port
output    HSELM4;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM4;
output [1 : 0]   HTRANSM4;
output    HWRITEM4;
output [2 : 0]   HSIZEM4;
output [2 : 0]   HBURSTM4;
output [3 : 0]   HPROTM4;
output [3 : 0]   HMASTERM4;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM4;
output    HMASTLOCKM4;
output    HREADYMUXM4;
`endif

`ifdef MASTER5
// Master 5 Output port
output    HSELM5;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM5;
output [1 : 0]   HTRANSM5;
output    HWRITEM5;
output [2 : 0]   HSIZEM5;
output [2 : 0]   HBURSTM5;
output [3 : 0]   HPROTM5;
output [3 : 0]   HMASTERM5;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM5;
output    HMASTLOCKM5;
output    HREADYMUXM5;
`endif

`ifdef MASTER6
// Master 6 Output port
output    HSELM6;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM6;
output [1 : 0]   HTRANSM6;
output    HWRITEM6;
output [2 : 0]   HSIZEM6;
output [2 : 0]   HBURSTM6;
output [3 : 0]   HPROTM6;
output [3 : 0]   HMASTERM6;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM6;
output    HMASTLOCKM6;
output    HREADYMUXM6;
`endif

`ifdef MASTER7
// Master 7 Output port
output    HSELM7;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM7;
output [1 : 0]   HTRANSM7;
output    HWRITEM7;
output [2 : 0]   HSIZEM7;
output [2 : 0]   HBURSTM7;
output [3 : 0]   HPROTM7;
output [3 : 0]   HMASTERM7;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM7;
output    HMASTLOCKM7;
output    HREADYMUXM7;
`endif

`ifdef MASTER8
// Master 8 Output port
output    HSELM8;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM8;
output [1 : 0]   HTRANSM8;
output    HWRITEM8;
output [2 : 0]   HSIZEM8;
output [2 : 0]   HBURSTM8;
output [3 : 0]   HPROTM8;
output [3 : 0]   HMASTERM8;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM8;
output    HMASTLOCKM8;
output    HREADYMUXM8;
`endif

`ifdef MASTER9
// Master 9 Output port
output    HSELM9;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM9;
output [1 : 0]   HTRANSM9;
output    HWRITEM9;
output [2 : 0]   HSIZEM9;
output [2 : 0]   HBURSTM9;
output [3 : 0]   HPROTM9;
output [3 : 0]   HMASTERM9;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM9;
output    HMASTLOCKM9;
output    HREADYMUXM9;
`endif

`ifdef MASTER10
// Master 10 Output port
output    HSELM10;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM10;
output [1 : 0]   HTRANSM10;
output    HWRITEM10;
output [2 : 0]   HSIZEM10;
output [2 : 0]   HBURSTM10;
output [3 : 0]   HPROTM10;
output [3 : 0]   HMASTERM10;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM10;
output    HMASTLOCKM10;
output    HREADYMUXM10;
`endif

`ifdef MASTER11
// Master 11 Output port
output    HSELM11;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM11;
output [1 : 0]   HTRANSM11;
output    HWRITEM11;
output [2 : 0]   HSIZEM11;
output [2 : 0]   HBURSTM11;
output [3 : 0]   HPROTM11;
output [3 : 0]   HMASTERM11;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM11;
output    HMASTLOCKM11;
output    HREADYMUXM11;
`endif

`ifdef MASTER12
// Master 12 Output port
output    HSELM12;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM12;
output [1 : 0]   HTRANSM12;
output    HWRITEM12;
output [2 : 0]   HSIZEM12;
output [2 : 0]   HBURSTM12;
output [3 : 0]   HPROTM12;
output [3 : 0]   HMASTERM12;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM12;
output    HMASTLOCKM12;
output    HREADYMUXM12;
`endif

`ifdef MASTER13
// Master 13 Output port
output    HSELM13;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM13;
output [1 : 0]   HTRANSM13;
output    HWRITEM13;
output [2 : 0]   HSIZEM13;
output [2 : 0]   HBURSTM13;
output [3 : 0]   HPROTM13;
output [3 : 0]   HMASTERM13;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM13;
output    HMASTLOCKM13;
output    HREADYMUXM13;
`endif

`ifdef MASTER14
// Master 14 Output port
output    HSELM14;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM14;
output [1 : 0]   HTRANSM14;
output    HWRITEM14;
output [2 : 0]   HSIZEM14;
output [2 : 0]   HBURSTM14;
output [3 : 0]   HPROTM14;
output [3 : 0]   HMASTERM14;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM14;
output    HMASTLOCKM14;
output    HREADYMUXM14;
`endif

`ifdef MASTER15
// Master 15 Output port
output    HSELM15;
output [`AHB_ADDR_WIDTH - 1 : 0]   HADDRM15;
output [1 : 0]   HTRANSM15;
output    HWRITEM15;
output [2 : 0]   HSIZEM15;
output [2 : 0]   HBURSTM15;
output [3 : 0]   HPROTM15;
output [3 : 0]   HMASTERM15;
output [`AHB_DATA_WIDTH - 1 : 0]   HWDATAM15;
output    HMASTLOCKM15;
output    HREADYMUXM15;
`endif


`ifdef SLAVE0
// Slave 0 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS0;
output   HREADYOUTS0;
output [1 : 0]  HRESPS0;
`endif

`ifdef SLAVE1
// Slave 1 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS1;
output   HREADYOUTS1;
output [1 : 0]  HRESPS1;
`endif

`ifdef SLAVE2
// Slave 2 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS2;
output   HREADYOUTS2;
output [1 : 0]  HRESPS2;
`endif

`ifdef SLAVE3
// Slave 3 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS3;
output   HREADYOUTS3;
output [1 : 0]  HRESPS3;
`endif

`ifdef SLAVE4
// Slave 4 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS4;
output   HREADYOUTS4;
output [1 : 0]  HRESPS4;
`endif

`ifdef SLAVE5
// Slave 5 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS5;
output   HREADYOUTS5;
output [1 : 0]  HRESPS5;
`endif

`ifdef SLAVE6
// Slave 6 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS6;
output   HREADYOUTS6;
output [1 : 0]  HRESPS6;
`endif

`ifdef SLAVE7
// Slave 7 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS7;
output   HREADYOUTS7;
output [1 : 0]  HRESPS7;
`endif

`ifdef SLAVE8
// Slave 8 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS8;
output   HREADYOUTS8;
output [1 : 0]  HRESPS8;
`endif

`ifdef SLAVE9
// Slave 9 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS9;
output   HREADYOUTS9;
output [1 : 0]  HRESPS9;
`endif

`ifdef SLAVE10
// Slave 10 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS10;
output   HREADYOUTS10;
output [1 : 0]  HRESPS10;
`endif

`ifdef SLAVE11
// Slave 11 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS11;
output   HREADYOUTS11;
output [1 : 0]  HRESPS11;
`endif

`ifdef SLAVE12
// Slave 12 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS12;
output   HREADYOUTS12;
output [1 : 0]  HRESPS12;
`endif

`ifdef SLAVE13
// Slave 13 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS13;
output   HREADYOUTS13;
output [1 : 0]  HRESPS13;
`endif

`ifdef SLAVE14
// Slave 14 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS14;
output   HREADYOUTS14;
output [1 : 0]  HRESPS14;
`endif

`ifdef SLAVE15
// Slave 15 Output port
output [`AHB_DATA_WIDTH - 1 : 0]  HRDATAS15;
output   HREADYOUTS15;
output [1 : 0]  HRESPS15;
`endif


output   SCANOUTHCLK;

assign SCANOUTHCLK = 1'b0;


wire  [`NUM_OF_SLAVES * `AHB_ADDR_WIDTH - 1 : 0] haddr_2_master_if;
wire  [`NUM_OF_SLAVES * 2 - 1 : 0] htran_2_master_if;
wire  [`NUM_OF_SLAVES - 1 : 0] hwrite_2_master_if;
wire  [`NUM_OF_SLAVES * 3 - 1 : 0] hsize_2_master_if;
wire  [`NUM_OF_SLAVES * 3 - 1 : 0] hburst_2_master_if;
wire  [`NUM_OF_SLAVES * 4 - 1 : 0] hprot_2_master_if;
wire  [`NUM_OF_SLAVES - 1 : 0] hready_2_master_if;
wire  [`NUM_OF_SLAVES * `AHB_DATA_WIDTH - 1 : 0] hwdata_2_master_if;

wire  [`NUM_OF_MASTERS * 2 - 1 : 0] s_hresp_from_all_slave;
wire  [`NUM_OF_MASTERS - 1 : 0] s_hready_from_all_slave;
wire  [`NUM_OF_MASTERS * `AHB_DATA_WIDTH - 1 : 0] s_hrdata_from_all_slave;


wire [`NUM_OF_SLAVES - 1 : 0] req_2_m0;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m1;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m2;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m3;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m4;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m5;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m6;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m7;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m8;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m9;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m10;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m11;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m12;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m13;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m14;
wire [`NUM_OF_SLAVES - 1 : 0] req_2_m15;


wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m0;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m1;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m2;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m3;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m4;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m5;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m6;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m7;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m8;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m9;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m10;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m11;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m12;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m13;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m14;
wire [`NUM_OF_SLAVES - 1 : 0] gnt_from_m15;


wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s0;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s0;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s1;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s1;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s2;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s2;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s3;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s3;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s4;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s4;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s5;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s5;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s6;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s6;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s7;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s7;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s8;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s8;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s9;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s9;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s10;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s10;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s11;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s11;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s12;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s12;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s13;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s13;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s14;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s14;
wire [`NUM_OF_MASTERS - 1 : 0]  req_from_s15;
wire [`NUM_OF_MASTERS - 1 : 0]  gnt_2_s15;



// slave instantiation
// It will be instantiated NUM_OF_SLAVES times

`ifdef SLAVE0
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s0;
wire [1 : 0]  htrans_int_s0;
wire   hwrite_int_s0;
wire [2 : 0]  hsize_int_s0;
wire [2 : 0]  hburst_int_s0;
wire [3 : 0]  hprot_int_s0;
   

slave_if i_s0 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS0),
   .haddr(HADDRS0),
   .htrans(HTRANSS0),
   .hwrite(HWRITES0),
   .hsize(HSIZES0),
   .hburst(HBURSTS0),
   .hprot(HPROTS0),
   .hready(HREADYS0),

   .gnt(gnt_2_s0[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS0),
   .hready_out(HREADYOUTS0),
   .hrdata_out(HRDATAS0),
   .haddr_int(haddr_int_s0),
   .htrans_int(htrans_int_s0),
   .hwrite_int(hwrite_int_s0),
   .hsize_int(hsize_int_s0),
   .hburst_int(hburst_int_s0),
   .hprot_int(hprot_int_s0),
   
   .req(req_from_s0)

);

assign haddr_2_master_if[`AHB_ADDR_WIDTH - 1 : 0] = haddr_int_s0;
assign htran_2_master_if[1 : 0] = htrans_int_s0;
assign hwrite_2_master_if[0] = hwrite_int_s0;
assign hsize_2_master_if[2 : 0] = hsize_int_s0;
assign hburst_2_master_if[2 : 0] = hburst_int_s0;
assign hprot_2_master_if[3 : 0] = hprot_int_s0;
assign hready_2_master_if[0] = HREADYS0;
assign hwdata_2_master_if[`AHB_DATA_WIDTH - 1 : 0] = HWDATAS0;

assign gnt_2_s0 = { gnt_from_m15[0],  gnt_from_m14[0], gnt_from_m13[0], 
                    gnt_from_m12[0],  gnt_from_m11[0], gnt_from_m10[0], 
                    gnt_from_m9[0],   gnt_from_m8[0],  gnt_from_m7[0],
                    gnt_from_m6[0],   gnt_from_m5[0],  gnt_from_m4[0], 
                    gnt_from_m3[0],   gnt_from_m2[0],  gnt_from_m1[0], 
                    gnt_from_m0[0] };
`endif



`ifdef SLAVE1
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s1;
wire [1 : 0]  htrans_int_s1;
wire   hwrite_int_s1;
wire [2 : 0]  hsize_int_s1;
wire [2 : 0]  hburst_int_s1;
wire [3 : 0]  hprot_int_s1;
   



slave_if i_s1 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS1),
   .haddr(HADDRS1),
   .htrans(HTRANSS1),
   .hwrite(HWRITES1),
   .hsize(HSIZES1),
   .hburst(HBURSTS1),
   .hprot(HPROTS1),
   .hready(HREADYS1),

   .gnt(gnt_2_s1[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS1),
   .hready_out(HREADYOUTS1),
   .hrdata_out(HRDATAS1),
   .haddr_int(haddr_int_s1),
   .htrans_int(htrans_int_s1),
   .hwrite_int(hwrite_int_s1),
   .hsize_int(hsize_int_s1),
   .hburst_int(hburst_int_s1),
   .hprot_int(hprot_int_s1),
   
   .req(req_from_s1)

);

assign haddr_2_master_if[2 * `AHB_ADDR_WIDTH - 1 : `AHB_ADDR_WIDTH] = haddr_int_s1;
assign htran_2_master_if[2 * 2 - 1 : 2] = htrans_int_s1;
assign hwrite_2_master_if[1] = hwrite_int_s1;
assign hsize_2_master_if[2 * 3 - 1: 3] = hsize_int_s1;
assign hburst_2_master_if[2 * 3  - 1: 3] = hburst_int_s1;
assign hprot_2_master_if[2 * 4 - 1 : 4] = hprot_int_s1;
assign hready_2_master_if[1] = HREADYS1;
assign hwdata_2_master_if[2 * `AHB_DATA_WIDTH - 1 : `AHB_DATA_WIDTH] = HWDATAS1;

assign gnt_2_s1 = { gnt_from_m15[1],  gnt_from_m14[1], gnt_from_m13[1], 
                    gnt_from_m12[1],  gnt_from_m11[1], gnt_from_m10[1],
                    gnt_from_m9[1],   gnt_from_m8[1],  gnt_from_m7[1],
                    gnt_from_m6[1],   gnt_from_m5[1],  gnt_from_m4[1], 
                    gnt_from_m3[1],   gnt_from_m2[1],  gnt_from_m1[1], 
                    gnt_from_m0[1] };
`endif


`ifdef SLAVE2
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s2;
wire [1 : 0]  htrans_int_s2;
wire   hwrite_int_s2;
wire [2 : 0]  hsize_int_s2;
wire [2 : 0]  hburst_int_s2;
wire [3 : 0]  hprot_int_s2;
   

slave_if i_s2 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS2),
   .haddr(HADDRS2),
   .htrans(HTRANSS2),
   .hwrite(HWRITES2),
   .hsize(HSIZES2),
   .hburst(HBURSTS2),
   .hprot(HPROTS2),
   .hready(HREADYS2),

   .gnt(gnt_2_s2[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS2),
   .hready_out(HREADYOUTS2),
   .hrdata_out(HRDATAS2),
   .haddr_int(haddr_int_s2),
   .htrans_int(htrans_int_s2),
   .hwrite_int(hwrite_int_s2),
   .hsize_int(hsize_int_s2),
   .hburst_int(hburst_int_s2),
   .hprot_int(hprot_int_s2),
   
   .req(req_from_s2)

);

assign haddr_2_master_if[3 * `AHB_ADDR_WIDTH - 1 : 2 * `AHB_ADDR_WIDTH] = haddr_int_s2;
assign htran_2_master_if[3 * 2 - 1 : 2 * 2] = htrans_int_s2;
assign hwrite_2_master_if[2] = hwrite_int_s2;
assign hsize_2_master_if[3 * 3 - 1: 2 * 3] = hsize_int_s2;
assign hburst_2_master_if[3 * 3  - 1: 2 * 3] = hburst_int_s2;
assign hprot_2_master_if[3 * 4 - 1 : 2 * 4] = hprot_int_s2;
assign hready_2_master_if[2] = HREADYS2;
assign hwdata_2_master_if[3 * `AHB_DATA_WIDTH - 1 : 2 * `AHB_DATA_WIDTH] = HWDATAS2;

assign gnt_2_s2 = { gnt_from_m15[2],  gnt_from_m14[2], gnt_from_m13[2],
                    gnt_from_m12[2],  gnt_from_m11[2], gnt_from_m10[2], 
                    gnt_from_m9[2],   gnt_from_m8[2],  gnt_from_m7[2],
                    gnt_from_m6[2],   gnt_from_m5[2],  gnt_from_m4[2], 
                    gnt_from_m3[2],   gnt_from_m2[2],  gnt_from_m1[2], 
                    gnt_from_m0[2] };
`endif


`ifdef SLAVE3
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s3;
wire [1 : 0]  htrans_int_s3;
wire   hwrite_int_s3;
wire [2 : 0]  hsize_int_s3;
wire [2 : 0]  hburst_int_s3;
wire [3 : 0]  hprot_int_s3;
   

slave_if i_s3 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS3),
   .haddr(HADDRS3),
   .htrans(HTRANSS3),
   .hwrite(HWRITES3),
   .hsize(HSIZES3),
   .hburst(HBURSTS3),
   .hprot(HPROTS3),
   .hready(HREADYS3),

   .gnt(gnt_2_s3[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS3),
   .hready_out(HREADYOUTS3),
   .hrdata_out(HRDATAS3),
   .haddr_int(haddr_int_s3),
   .htrans_int(htrans_int_s3),
   .hwrite_int(hwrite_int_s3),
   .hsize_int(hsize_int_s3),
   .hburst_int(hburst_int_s3),
   .hprot_int(hprot_int_s3),
   
   .req(req_from_s3)

);

assign haddr_2_master_if[4 * `AHB_ADDR_WIDTH - 1 : 3 * `AHB_ADDR_WIDTH] = haddr_int_s3;
assign htran_2_master_if[4 * 2 - 1 : 3 * 2] = htrans_int_s3;
assign hwrite_2_master_if[3] = hwrite_int_s3;
assign hsize_2_master_if[4 * 3 - 1: 3 * 3] = hsize_int_s3;
assign hburst_2_master_if[4 * 3  - 1: 3 * 3] = hburst_int_s3;
assign hprot_2_master_if[4 * 4 - 1 : 3 * 4] = hprot_int_s3;
assign hready_2_master_if[3] = HREADYS3;
assign hwdata_2_master_if[4 * `AHB_DATA_WIDTH - 1 : 3 * `AHB_DATA_WIDTH] = HWDATAS3;

assign gnt_2_s3 = { gnt_from_m15[3],  gnt_from_m14[3], gnt_from_m13[3], 
                    gnt_from_m12[3],  gnt_from_m11[3], gnt_from_m10[3], 
                    gnt_from_m9[3],   gnt_from_m8[3],  gnt_from_m7[3],
                    gnt_from_m6[3],   gnt_from_m5[3],  gnt_from_m4[3], 
                    gnt_from_m3[3],   gnt_from_m2[3],  gnt_from_m1[3], 
                    gnt_from_m0[3] };

`endif

`ifdef SLAVE4
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s4;
wire [1 : 0]  htrans_int_s4;
wire   hwrite_int_s4;
wire [2 : 0]  hsize_int_s4;
wire [2 : 0]  hburst_int_s4;
wire [3 : 0]  hprot_int_s4;
   

slave_if i_s4 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS4),
   .haddr(HADDRS4),
   .htrans(HTRANSS4),
   .hwrite(HWRITES4),
   .hsize(HSIZES4),
   .hburst(HBURSTS4),
   .hprot(HPROTS4),
   .hready(HREADYS4),

   .gnt(gnt_2_s4[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS4),
   .hready_out(HREADYOUTS4),
   .hrdata_out(HRDATAS4),
   .haddr_int(haddr_int_s4),
   .htrans_int(htrans_int_s4),
   .hwrite_int(hwrite_int_s4),
   .hsize_int(hsize_int_s4),
   .hburst_int(hburst_int_s4),
   .hprot_int(hprot_int_s4),
   
   .req(req_from_s4)

);

assign haddr_2_master_if[5 * `AHB_ADDR_WIDTH - 1 : 4 * `AHB_ADDR_WIDTH] = haddr_int_s4;
assign htran_2_master_if[5 * 2 - 1 : 4 * 2] = htrans_int_s4;
assign hwrite_2_master_if[4] = hwrite_int_s4;
assign hsize_2_master_if[5 * 3 - 1: 4 * 3] = hsize_int_s4;
assign hburst_2_master_if[5 * 3  - 1: 4 * 3] = hburst_int_s4;
assign hprot_2_master_if[5 * 4 - 1 : 4 * 4] = hprot_int_s4;
assign hready_2_master_if[4] = HREADYS4;
assign hwdata_2_master_if[5 * `AHB_DATA_WIDTH - 1 : 4 * `AHB_DATA_WIDTH] = HWDATAS4;

assign gnt_2_s4 = { gnt_from_m15[4],  gnt_from_m14[4], gnt_from_m13[4], 
                    gnt_from_m12[4],  gnt_from_m11[4], gnt_from_m10[4], 
                    gnt_from_m9[4],   gnt_from_m8[4],  gnt_from_m7[4],
                    gnt_from_m6[4],   gnt_from_m5[4],  gnt_from_m4[4], 
                    gnt_from_m3[4],   gnt_from_m2[4],  gnt_from_m1[4], 
                    gnt_from_m0[4] };

`endif

`ifdef SLAVE5
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s5;
wire [1 : 0]  htrans_int_s5;
wire   hwrite_int_s5;
wire [2 : 0]  hsize_int_s5;
wire [2 : 0]  hburst_int_s5;
wire [3 : 0]  hprot_int_s5;
   


slave_if i_s5 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS5),
   .haddr(HADDRS5),
   .htrans(HTRANSS5),
   .hwrite(HWRITES5),
   .hsize(HSIZES5),
   .hburst(HBURSTS5),
   .hprot(HPROTS5),
   .hready(HREADYS5),

   .gnt(gnt_2_s5[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS5),
   .hready_out(HREADYOUTS5),
   .hrdata_out(HRDATAS5),
   .haddr_int(haddr_int_s5),
   .htrans_int(htrans_int_s5),
   .hwrite_int(hwrite_int_s5),
   .hsize_int(hsize_int_s5),
   .hburst_int(hburst_int_s5),
   .hprot_int(hprot_int_s5),
   
   .req(req_from_s5)

);

assign haddr_2_master_if[6 * `AHB_ADDR_WIDTH - 1 : 5 * `AHB_ADDR_WIDTH] = haddr_int_s5;
assign htran_2_master_if[6 * 2 - 1 : 5 * 2] = htrans_int_s5;
assign hwrite_2_master_if[5] = hwrite_int_s5;
assign hsize_2_master_if[6 * 3 - 1: 5 * 3] = hsize_int_s5;
assign hburst_2_master_if[6 * 3  - 1: 5 * 3] = hburst_int_s5;
assign hprot_2_master_if[6 * 4 - 1 : 5 * 4] = hprot_int_s5;
assign hready_2_master_if[5] = HREADYS5;
assign hwdata_2_master_if[6 * `AHB_DATA_WIDTH - 1 : 5 * `AHB_DATA_WIDTH] = HWDATAS5;

assign gnt_2_s5 = { gnt_from_m15[5],  gnt_from_m14[5], gnt_from_m13[5], 
                    gnt_from_m12[5],  gnt_from_m11[5], gnt_from_m10[5], 
                    gnt_from_m9[5],   gnt_from_m8[5],  gnt_from_m7[5],
                    gnt_from_m6[5],   gnt_from_m5[5],  gnt_from_m4[5], 
                    gnt_from_m3[5],   gnt_from_m2[5],  gnt_from_m1[5], 
                    gnt_from_m0[5] };
`endif


`ifdef SLAVE6
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s6;
wire [1 : 0]  htrans_int_s6;
wire   hwrite_int_s6;
wire [2 : 0]  hsize_int_s6;
wire [2 : 0]  hburst_int_s6;
wire [3 : 0]  hprot_int_s6;
   

slave_if i_s6 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS6),
   .haddr(HADDRS6),
   .htrans(HTRANSS6),
   .hwrite(HWRITES6),
   .hsize(HSIZES6),
   .hburst(HBURSTS6),
   .hprot(HPROTS6),
   .hready(HREADYS6),

   .gnt(gnt_2_s6[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS6),
   .hready_out(HREADYOUTS6),
   .hrdata_out(HRDATAS6),
   .haddr_int(haddr_int_s6),
   .htrans_int(htrans_int_s6),
   .hwrite_int(hwrite_int_s6),
   .hsize_int(hsize_int_s6),
   .hburst_int(hburst_int_s6),
   .hprot_int(hprot_int_s6),
   
   .req(req_from_s6)

);

assign haddr_2_master_if[7 * `AHB_ADDR_WIDTH - 1 : 6 * `AHB_ADDR_WIDTH] = haddr_int_s6;
assign htran_2_master_if[7 * 2 - 1 : 6 * 2] = htrans_int_s6;
assign hwrite_2_master_if[6] = hwrite_int_s6;
assign hsize_2_master_if[7 * 3 - 1: 6 * 3] = hsize_int_s6;
assign hburst_2_master_if[7 * 3  - 1: 6 * 3] = hburst_int_s6;
assign hprot_2_master_if[7 * 4 - 1 : 6 * 4] = hprot_int_s6;
assign hready_2_master_if[6] = HREADYS6;
assign hwdata_2_master_if[7 * `AHB_DATA_WIDTH - 1 : 6 * `AHB_DATA_WIDTH] = HWDATAS6;

assign gnt_2_s6 = { gnt_from_m15[6],  gnt_from_m14[6], gnt_from_m13[6], 
                    gnt_from_m12[6],  gnt_from_m11[6], gnt_from_m10[6],
                    gnt_from_m9[6],   gnt_from_m8[6],  gnt_from_m7[6],
                    gnt_from_m6[6],   gnt_from_m5[6],  gnt_from_m4[6], 
                    gnt_from_m3[6],   gnt_from_m2[6],  gnt_from_m1[6], 
                    gnt_from_m0[6] };
`endif


`ifdef SLAVE7
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s7;
wire [1 : 0]  htrans_int_s7;
wire   hwrite_int_s7;
wire [2 : 0]  hsize_int_s7;
wire [2 : 0]  hburst_int_s7;
wire [3 : 0]  hprot_int_s7;
   

slave_if i_s7 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS7),
   .haddr(HADDRS7),
   .htrans(HTRANSS7),
   .hwrite(HWRITES7),
   .hsize(HSIZES7),
   .hburst(HBURSTS7),
   .hprot(HPROTS7),
   .hready(HREADYS7),

   .gnt(gnt_2_s7[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS7),
   .hready_out(HREADYOUTS7),
   .hrdata_out(HRDATAS7),
   .haddr_int(haddr_int_s7),
   .htrans_int(htrans_int_s7),
   .hwrite_int(hwrite_int_s7),
   .hsize_int(hsize_int_s7),
   .hburst_int(hburst_int_s7),
   .hprot_int(hprot_int_s7),
   
   .req(req_from_s7)

);

assign haddr_2_master_if[8 * `AHB_ADDR_WIDTH - 1 : 7 * `AHB_ADDR_WIDTH] = haddr_int_s7;
assign htran_2_master_if[8 * 2 - 1 : 7 * 2] = htrans_int_s7;
assign hwrite_2_master_if[7] = hwrite_int_s7;
assign hsize_2_master_if[8 * 3 - 1: 7 * 3] = hsize_int_s7;
assign hburst_2_master_if[8 * 3  - 1: 7 * 3] = hburst_int_s7;
assign hprot_2_master_if[8 * 4 - 1 : 7 * 4] = hprot_int_s7;
assign hready_2_master_if[7] = HREADYS7;
assign hwdata_2_master_if[8 * `AHB_DATA_WIDTH - 1 : 7 * `AHB_DATA_WIDTH] = HWDATAS7;

assign gnt_2_s7 = { gnt_from_m15[7],  gnt_from_m14[7], gnt_from_m13[7], 
                    gnt_from_m12[7],  gnt_from_m11[7], gnt_from_m10[7], 
                    gnt_from_m9[7],   gnt_from_m8[7],  gnt_from_m7[7],
                    gnt_from_m6[7],   gnt_from_m5[7],  gnt_from_m4[7], 
                    gnt_from_m3[7],   gnt_from_m2[7],  gnt_from_m1[7], 
                    gnt_from_m0[7] };
`endif



`ifdef SLAVE8
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s8;
wire [1 : 0]  htrans_int_s8;
wire   hwrite_int_s8;
wire [2 : 0]  hsize_int_s8;
wire [2 : 0]  hburst_int_s8;
wire [3 : 0]  hprot_int_s8;
   

slave_if i_s8 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS8),
   .haddr(HADDRS8),
   .htrans(HTRANSS8),
   .hwrite(HWRITES8),
   .hsize(HSIZES8),
   .hburst(HBURSTS8),
   .hprot(HPROTS8),
   .hready(HREADYS8),

   .gnt(gnt_2_s8[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS8),
   .hready_out(HREADYOUTS8),
   .hrdata_out(HRDATAS8),
   .haddr_int(haddr_int_s8),
   .htrans_int(htrans_int_s8),
   .hwrite_int(hwrite_int_s8),
   .hsize_int(hsize_int_s8),
   .hburst_int(hburst_int_s8),
   .hprot_int(hprot_int_s8),
   
   .req(req_from_s8)

);

assign haddr_2_master_if[9 * `AHB_ADDR_WIDTH - 1 : 8 * `AHB_ADDR_WIDTH] = haddr_int_s8;
assign htran_2_master_if[9 * 2 - 1 : 8 * 2] = htrans_int_s8;
assign hwrite_2_master_if[8] = hwrite_int_s8;
assign hsize_2_master_if[9 * 3 - 1: 8 * 3] = hsize_int_s8;
assign hburst_2_master_if[9 * 3  - 1: 8 * 3] = hburst_int_s8;
assign hprot_2_master_if[9 * 4 - 1 : 8 * 4] = hprot_int_s8;
assign hready_2_master_if[8] = HREADYS8;
assign hwdata_2_master_if[9 * `AHB_DATA_WIDTH - 1 : 8 * `AHB_DATA_WIDTH] = HWDATAS8;

assign gnt_2_s8 = { gnt_from_m15[8],  gnt_from_m14[8], gnt_from_m13[8],
                    gnt_from_m12[8],  gnt_from_m11[8], gnt_from_m10[8], 
                    gnt_from_m9[8],   gnt_from_m8[8],  gnt_from_m7[8],
                    gnt_from_m6[8],   gnt_from_m5[8],  gnt_from_m4[8], 
                    gnt_from_m3[8],   gnt_from_m2[8],  gnt_from_m1[8], 
                    gnt_from_m0[8] };

`endif

`ifdef SLAVE9
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s9;
wire [1 : 0]  htrans_int_s9;
wire   hwrite_int_s9;
wire [2 : 0]  hsize_int_s9;
wire [2 : 0]  hburst_int_s9;
wire [3 : 0]  hprot_int_s9;
   

slave_if i_s9 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS9),
   .haddr(HADDRS9),
   .htrans(HTRANSS9),
   .hwrite(HWRITES9),
   .hsize(HSIZES9),
   .hburst(HBURSTS9),
   .hprot(HPROTS9),
   .hready(HREADYS9),

   .gnt(gnt_2_s9[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS9),
   .hready_out(HREADYOUTS9),
   .hrdata_out(HRDATAS9),
   .haddr_int(haddr_int_s9),
   .htrans_int(htrans_int_s9),
   .hwrite_int(hwrite_int_s9),
   .hsize_int(hsize_int_s9),
   .hburst_int(hburst_int_s9),
   .hprot_int(hprot_int_s9),
   
   .req(req_from_s9)

);

assign haddr_2_master_if[10 * `AHB_ADDR_WIDTH - 1 : 9 * `AHB_ADDR_WIDTH] = haddr_int_s9;
assign htran_2_master_if[10 * 2 - 1 : 9 * 2] = htrans_int_s9;
assign hwrite_2_master_if[9] = hwrite_int_s9;
assign hsize_2_master_if[10 * 3 - 1: 9 * 3] = hsize_int_s9;
assign hburst_2_master_if[10 * 3  - 1: 9 * 3] = hburst_int_s9;
assign hprot_2_master_if[10 * 4 - 1 : 9 * 4] = hprot_int_s9;
assign hready_2_master_if[9] = HREADYS9;
assign hwdata_2_master_if[10 * `AHB_DATA_WIDTH - 1 : 9 * `AHB_DATA_WIDTH] = HWDATAS9;

assign gnt_2_s9 = { gnt_from_m15[9],  gnt_from_m14[9], gnt_from_m13[9], 
                    gnt_from_m12[9],  gnt_from_m11[9], gnt_from_m10[9], 
                    gnt_from_m9[9],   gnt_from_m8[9],  gnt_from_m7[9],
                    gnt_from_m6[9],   gnt_from_m5[9],  gnt_from_m4[9], 
                    gnt_from_m3[9],   gnt_from_m2[9],  gnt_from_m1[9], 
                    gnt_from_m0[9] };
`endif


`ifdef SLAVE10
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s10;
wire [1 : 0]  htrans_int_s10;
wire   hwrite_int_s10;
wire [2 : 0]  hsize_int_s10;
wire [2 : 0]  hburst_int_s10;
wire [3 : 0]  hprot_int_s10;
   

slave_if i_s10 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS10),
   .haddr(HADDRS10),
   .htrans(HTRANSS10),
   .hwrite(HWRITES10),
   .hsize(HSIZES10),
   .hburst(HBURSTS10),
   .hprot(HPROTS10),
   .hready(HREADYS10),

   .gnt(gnt_2_s10[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS10),
   .hready_out(HREADYOUTS10),
   .hrdata_out(HRDATAS10),
   .haddr_int(haddr_int_s10),
   .htrans_int(htrans_int_s10),
   .hwrite_int(hwrite_int_s10),
   .hsize_int(hsize_int_s10),
   .hburst_int(hburst_int_s10),
   .hprot_int(hprot_int_s10),
   
   .req(req_from_s10)

);

assign haddr_2_master_if[11 * `AHB_ADDR_WIDTH - 1 : 10 * `AHB_ADDR_WIDTH] = haddr_int_s10;
assign htran_2_master_if[11 * 2 - 1 : 10 * 2] = htrans_int_s10;
assign hwrite_2_master_if[10] = hwrite_int_s10;
assign hsize_2_master_if[11 * 3 - 1: 10 * 3] = hsize_int_s10;
assign hburst_2_master_if[11 * 3  - 1: 10 * 3] = hburst_int_s10;
assign hprot_2_master_if[11 * 4 - 1 : 10 * 4] = hprot_int_s10;
assign hready_2_master_if[10] = HREADYS10;
assign hwdata_2_master_if[11 * `AHB_DATA_WIDTH - 1 : 10 * `AHB_DATA_WIDTH] = HWDATAS10;

assign gnt_2_s10 = { gnt_from_m15[10],  gnt_from_m14[10], gnt_from_m13[10], 
                     gnt_from_m12[10],  gnt_from_m11[10], gnt_from_m10[10], 
                     gnt_from_m9[10],   gnt_from_m8[10],  gnt_from_m7[10],
                     gnt_from_m6[10],   gnt_from_m5[10],  gnt_from_m4[10], 
                     gnt_from_m3[10],   gnt_from_m2[10],  gnt_from_m1[10], 
                     gnt_from_m0[10] };
`endif



`ifdef SLAVE11
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s11;
wire [1 : 0]  htrans_int_s11;
wire   hwrite_int_s11;
wire [2 : 0]  hsize_int_s11;
wire [2 : 0]  hburst_int_s11;
wire [3 : 0]  hprot_int_s11;
   

slave_if i_s11 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS11),
   .haddr(HADDRS11),
   .htrans(HTRANSS11),
   .hwrite(HWRITES11),
   .hsize(HSIZES11),
   .hburst(HBURSTS11),
   .hprot(HPROTS11),
   .hready(HREADYS11),

   .gnt(gnt_2_s11[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS11),
   .hready_out(HREADYOUTS11),
   .hrdata_out(HRDATAS11),
   .haddr_int(haddr_int_s11),
   .htrans_int(htrans_int_s11),
   .hwrite_int(hwrite_int_s11),
   .hsize_int(hsize_int_s11),
   .hburst_int(hburst_int_s11),
   .hprot_int(hprot_int_s11),
   
   .req(req_from_s11)

);

assign haddr_2_master_if[12 * `AHB_ADDR_WIDTH - 1 : 11 * `AHB_ADDR_WIDTH] = haddr_int_s11;
assign htran_2_master_if[12 * 2 - 1 : 11 * 2] = htrans_int_s11;
assign hwrite_2_master_if[11] = hwrite_int_s11;
assign hsize_2_master_if[12 * 3 - 1: 11 * 3] = hsize_int_s11;
assign hburst_2_master_if[12 * 3  - 1: 11 * 3] = hburst_int_s11;
assign hprot_2_master_if[12 * 4 - 1 : 11 * 4] = hprot_int_s11;
assign hready_2_master_if[11] = HREADYS11;
assign hwdata_2_master_if[12 * `AHB_DATA_WIDTH - 1 : 11 * `AHB_DATA_WIDTH] = HWDATAS11;

assign gnt_2_s11 = { gnt_from_m15[11],  gnt_from_m14[11], gnt_from_m13[11], 
                     gnt_from_m12[11],  gnt_from_m11[11], gnt_from_m10[11], 
                     gnt_from_m9[11],   gnt_from_m8[11],  gnt_from_m7[11],
                     gnt_from_m6[11],   gnt_from_m5[11],  gnt_from_m4[11], 
                     gnt_from_m3[11],   gnt_from_m2[11],  gnt_from_m1[11], 
                     gnt_from_m0[11] };
`endif


`ifdef SLAVE12
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s12;
wire [1 : 0]  htrans_int_s12;
wire   hwrite_int_s12;
wire [2 : 0]  hsize_int_s12;
wire [2 : 0]  hburst_int_s12;
wire [3 : 0]  hprot_int_s12;
   

slave_if i_s12 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS12),
   .haddr(HADDRS12),
   .htrans(HTRANSS12),
   .hwrite(HWRITES12),
   .hsize(HSIZES12),
   .hburst(HBURSTS12),
   .hprot(HPROTS12),
   .hready(HREADYS12),

   .gnt(gnt_2_s12[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS12),
   .hready_out(HREADYOUTS12),
   .hrdata_out(HRDATAS12),
   .haddr_int(haddr_int_s12),
   .htrans_int(htrans_int_s12),
   .hwrite_int(hwrite_int_s12),
   .hsize_int(hsize_int_s12),
   .hburst_int(hburst_int_s12),
   .hprot_int(hprot_int_s12),
   
   .req(req_from_s12)

);

assign haddr_2_master_if[13 * `AHB_ADDR_WIDTH - 1 : 12 * `AHB_ADDR_WIDTH] = haddr_int_s12;
assign htran_2_master_if[13 * 2 - 1 : 12 * 2] = htrans_int_s12;
assign hwrite_2_master_if[12] = hwrite_int_s12;
assign hsize_2_master_if[13 * 3 - 1: 12 * 3] = hsize_int_s12;
assign hburst_2_master_if[13 * 3  - 1: 12 * 3] = hburst_int_s12;
assign hprot_2_master_if[13 * 4 - 1 : 12 * 4] = hprot_int_s12;
assign hready_2_master_if[12] = HREADYS12;
assign hwdata_2_master_if[13 * `AHB_DATA_WIDTH - 1 : 12 * `AHB_DATA_WIDTH] = HWDATAS12;

assign gnt_2_s12 = { gnt_from_m15[12],  gnt_from_m14[12], gnt_from_m13[12], 
                     gnt_from_m12[12],  gnt_from_m11[12], gnt_from_m10[12], 
                     gnt_from_m9[12],   gnt_from_m8[12],  gnt_from_m7[12],
                     gnt_from_m6[12],   gnt_from_m5[12],  gnt_from_m4[12], 
                     gnt_from_m3[12],   gnt_from_m2[12],  gnt_from_m1[12], 
                     gnt_from_m0[12] };

`endif


`ifdef SLAVE13
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s13;
wire [1 : 0]  htrans_int_s13;
wire   hwrite_int_s13;
wire [2 : 0]  hsize_int_s13;
wire [2 : 0]  hburst_int_s13;
wire [3 : 0]  hprot_int_s13;
   

slave_if i_s13 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS13),
   .haddr(HADDRS13),
   .htrans(HTRANSS13),
   .hwrite(HWRITES13),
   .hsize(HSIZES13),
   .hburst(HBURSTS13),
   .hprot(HPROTS13),
   .hready(HREADYS13),

   .gnt(gnt_2_s13[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS13),
   .hready_out(HREADYOUTS13),
   .hrdata_out(HRDATAS13),
   .haddr_int(haddr_int_s13),
   .htrans_int(htrans_int_s13),
   .hwrite_int(hwrite_int_s13),
   .hsize_int(hsize_int_s13),
   .hburst_int(hburst_int_s13),
   .hprot_int(hprot_int_s13),
   
   .req(req_from_s13)

);

assign haddr_2_master_if[14 * `AHB_ADDR_WIDTH - 1 : 13 * `AHB_ADDR_WIDTH] = haddr_int_s13;
assign htran_2_master_if[14 * 2 - 1 : 13 * 2] = htrans_int_s13;
assign hwrite_2_master_if[13] = hwrite_int_s13;
assign hsize_2_master_if[14 * 3 - 1: 13 * 3] = hsize_int_s13;
assign hburst_2_master_if[14 * 3  - 1: 13 * 3] = hburst_int_s13;
assign hprot_2_master_if[14 * 4 - 1 : 13 * 4] = hprot_int_s13;
assign hready_2_master_if[13] = HREADYS13;
assign hwdata_2_master_if[14 * `AHB_DATA_WIDTH - 1 : 13 * `AHB_DATA_WIDTH] = HWDATAS13;

assign gnt_2_s13 = { gnt_from_m15[13],  gnt_from_m14[13], gnt_from_m13[13], 
                     gnt_from_m12[13],  gnt_from_m11[13], gnt_from_m10[13], 
                     gnt_from_m9[13],   gnt_from_m8[13],  gnt_from_m7[13],
                     gnt_from_m6[13],   gnt_from_m5[13],  gnt_from_m4[13], 
                     gnt_from_m3[13],   gnt_from_m2[13],  gnt_from_m1[13], 
                     gnt_from_m0[13] };

`endif


`ifdef SLAVE14
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s14;
wire [1 : 0]  htrans_int_s14;
wire   hwrite_int_s14;
wire [2 : 0]  hsize_int_s14;
wire [2 : 0]  hburst_int_s14;
wire [3 : 0]  hprot_int_s14;
   

slave_if i_s14 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS14),
   .haddr(HADDRS14),
   .htrans(HTRANSS14),
   .hwrite(HWRITES14),
   .hsize(HSIZES14),
   .hburst(HBURSTS14),
   .hprot(HPROTS14),
   .hready(HREADYS14),

   .gnt(gnt_2_s14[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS14),
   .hready_out(HREADYOUTS14),
   .hrdata_out(HRDATAS14),
   .haddr_int(haddr_int_s14),
   .htrans_int(htrans_int_s14),
   .hwrite_int(hwrite_int_s14),
   .hsize_int(hsize_int_s14),
   .hburst_int(hburst_int_s14),
   .hprot_int(hprot_int_s14),
   
   .req(req_from_s14)

);

assign haddr_2_master_if[15 * `AHB_ADDR_WIDTH - 1 : 14 * `AHB_ADDR_WIDTH] = haddr_int_s14;
assign htran_2_master_if[15 * 2 - 1 : 14 * 2] = htrans_int_s14;
assign hwrite_2_master_if[14] = hwrite_int_s14;
assign hsize_2_master_if[15 * 3 - 1: 14 * 3] = hsize_int_s14;
assign hburst_2_master_if[15 * 3  - 1: 14 * 3] = hburst_int_s14;
assign hprot_2_master_if[15 * 4 - 1 : 14 * 4] = hprot_int_s14;
assign hready_2_master_if[14] = HREADYS14;
assign hwdata_2_master_if[15 * `AHB_DATA_WIDTH - 1 : 14 * `AHB_DATA_WIDTH] = HWDATAS14;

assign gnt_2_s14 = { gnt_from_m15[14],  gnt_from_m14[14], gnt_from_m13[14], 
                     gnt_from_m12[14],  gnt_from_m11[14], gnt_from_m10[14], 
                     gnt_from_m9[14],   gnt_from_m8[14],  gnt_from_m7[14],
                     gnt_from_m6[14],   gnt_from_m5[14],  gnt_from_m4[14], 
                     gnt_from_m3[14],   gnt_from_m2[14],  gnt_from_m1[14], 
                     gnt_from_m0[14] };

`endif


`ifdef SLAVE15
wire [`AHB_ADDR_WIDTH - 1 : 0]  haddr_int_s15;
wire [1 : 0]  htrans_int_s15;
wire   hwrite_int_s15;
wire [2 : 0]  hsize_int_s15;
wire [2 : 0]  hburst_int_s15;
wire [3 : 0]  hprot_int_s15;
   

slave_if i_s15 (

   // input ports
   .hclk(HCLK),
   .hresetn(HRESETn),
   .hsel(HSELS15),
   .haddr(HADDRS15),
   .htrans(HTRANSS15),
   .hwrite(HWRITES15),
   .hsize(HSIZES15),
   .hburst(HBURSTS15),
   .hprot(HPROTS15),
   .hready(HREADYS15),

   .gnt(gnt_2_s15[`NUM_OF_MASTERS - 1 : 0]),   // From master interface
   .s_hresp_from_all_slave(s_hresp_from_all_slave),  // From master interface
   .s_hready_from_all_slave(s_hready_from_all_slave),  // From master interface
   .s_hrdata_from_all_slave(s_hrdata_from_all_slave),

   // output ports
   .hresp_out(HRESPS15),
   .hready_out(HREADYOUTS15),
   .hrdata_out(HRDATAS15),
   .haddr_int(haddr_int_s15),
   .htrans_int(htrans_int_s15),
   .hwrite_int(hwrite_int_s15),
   .hsize_int(hsize_int_s15),
   .hburst_int(hburst_int_s15),
   .hprot_int(hprot_int_s15),
   
   .req(req_from_s15)

);

assign haddr_2_master_if[16 * `AHB_ADDR_WIDTH - 1 : 15 * `AHB_ADDR_WIDTH] = haddr_int_s15;
assign htran_2_master_if[16 * 2 - 1 : 15 * 2] = htrans_int_s15;
assign hwrite_2_master_if[15] = hwrite_int_s15;
assign hsize_2_master_if[16 * 3 - 1: 15 * 3] = hsize_int_s15;
assign hburst_2_master_if[16 * 3  - 1: 15 * 3] = hburst_int_s15;
assign hprot_2_master_if[16 * 4 - 1 : 15 * 4] = hprot_int_s15;
assign hready_2_master_if[15] = HREADYS15;
assign hwdata_2_master_if[16 * `AHB_DATA_WIDTH - 1 : 15 * `AHB_DATA_WIDTH] = HWDATAS15;

assign gnt_2_s15 = { gnt_from_m15[15],  gnt_from_m14[15], gnt_from_m13[15], 
                     gnt_from_m12[15],  gnt_from_m11[15], gnt_from_m10[15], 
                     gnt_from_m9[15],   gnt_from_m8[15],  gnt_from_m7[15],
                     gnt_from_m6[15],   gnt_from_m5[15],  gnt_from_m4[15], 
                     gnt_from_m3[15],   gnt_from_m2[15],  gnt_from_m1[15], 
                     gnt_from_m0[15] };

`endif
///  Slave Instantiation done


// master instantiation
// It will be instantiated NUM_OF_MASTERS times

`ifdef MASTER0

wire  hready_from_m0;
wire [1 : 0] hresp_from_m0;

assign     HMASTLOCKM0 = 0;
assign HMASTERM0 = 4'b0;

master_if i_m0 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m0[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM0),
  .hresp_in_from_slave(HRESPM0),

  // output ports
  .m_hsel(HSELM0),
  .m_haddr(HADDRM0),
  .m_htrans(HTRANSM0),
  .m_hwrite(HWRITEM0),
  .m_hsize(HSIZEM0),
  .m_hburst(HBURSTM0),
  .m_hprot(HPROTM0),
  .m_hready(HREADYMUXM0),
  .m_hwdata(HWDATAM0),
  
  .hready_out_from_slave(hready_from_m0),
  .hresp_from_slave(hresp_from_m0),
  .gnt(gnt_from_m0)

);


assign s_hresp_from_all_slave[1 : 0]   =  hresp_from_m0;
assign s_hready_from_all_slave[0]  = hready_from_m0;
assign s_hrdata_from_all_slave[`AHB_DATA_WIDTH - 1 : 0]   = HRDATAM0;


assign req_2_m0 = { req_from_s15[0], req_from_s14[0], req_from_s13[0], 
                    req_from_s12[0], req_from_s11[0], req_from_s10[0], 
                    req_from_s9[0],  req_from_s8[0],  req_from_s7[0],
                    req_from_s6[0],  req_from_s5[0],  req_from_s4[0], 
                    req_from_s3[0],  req_from_s2[0],  req_from_s1[0], 
                    req_from_s0[0] };
`endif


`ifdef MASTER1
wire  hready_from_m1;
wire [1 : 0] hresp_from_m1;

assign     HMASTLOCKM1 = 0;
assign HMASTERM1 = 4'b0;


master_if i_m1 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m1[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM1),
  .hresp_in_from_slave(HRESPM1),

  // output ports
  .m_hsel(HSELM1),
  .m_haddr(HADDRM1),
  .m_htrans(HTRANSM1),
  .m_hwrite(HWRITEM1),
  .m_hsize(HSIZEM1),
  .m_hburst(HBURSTM1),
  .m_hprot(HPROTM1),
  .m_hready(HREADYMUXM1),
  .m_hwdata(HWDATAM1),
  
  .hready_out_from_slave(hready_from_m1),
  .hresp_from_slave(hresp_from_m1),
  .gnt(gnt_from_m1)

);


assign s_hresp_from_all_slave[2 * 2 - 1 : 2]   =  hresp_from_m1;
assign s_hready_from_all_slave[1]  = hready_from_m1;
assign s_hrdata_from_all_slave[2 * `AHB_DATA_WIDTH - 1 : `AHB_DATA_WIDTH]   = HRDATAM1;

assign req_2_m1 = { req_from_s15[1],  req_from_s14[1], req_from_s13[1], 
                    req_from_s12[1],  req_from_s11[1], req_from_s10[1], 
                    req_from_s9[1],   req_from_s8[1],  req_from_s7[1],
                    req_from_s6[1],   req_from_s5[1],  req_from_s4[1], 
                    req_from_s3[1],   req_from_s2[1],  req_from_s1[1], 
                    req_from_s0[1] };
`endif


`ifdef MASTER2
wire  hready_from_m2;
wire [1 : 0] hresp_from_m2;

assign     HMASTLOCKM2 = 0;
assign HMASTERM2 = 4'b0;


master_if i_m2 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m2[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM2),
  .hresp_in_from_slave(HRESPM2),

  // output ports
  .m_hsel(HSELM2),
  .m_haddr(HADDRM2),
  .m_htrans(HTRANSM2),
  .m_hwrite(HWRITEM2),
  .m_hsize(HSIZEM2),
  .m_hburst(HBURSTM2),
  .m_hprot(HPROTM2),
  .m_hready(HREADYMUXM2),
  .m_hwdata(HWDATAM2),
  
  .hready_out_from_slave(hready_from_m2),
  .hresp_from_slave(hresp_from_m2),
  .gnt(gnt_from_m2)

);


assign s_hresp_from_all_slave[3 * 2 - 1 : 2 * 2]   =  hresp_from_m2;
assign s_hready_from_all_slave[2]  = hready_from_m2;
assign s_hrdata_from_all_slave[3 * `AHB_DATA_WIDTH - 1 : 2 * `AHB_DATA_WIDTH]   = HRDATAM2;

assign req_2_m2 = { req_from_s15[2],  req_from_s14[2], req_from_s13[2], 
                    req_from_s12[2],  req_from_s11[2], req_from_s10[2], 
                    req_from_s9[2],   req_from_s8[2],  req_from_s7[2],
                    req_from_s6[2],   req_from_s5[2],  req_from_s4[2], 
                    req_from_s3[2],   req_from_s2[2],  req_from_s1[2], 
                    req_from_s0[2] };
`endif


`ifdef MASTER3
wire  hready_from_m3;
wire [1 : 0] hresp_from_m3;

assign     HMASTLOCKM3 = 0;
assign HMASTERM3 = 4'b0;


master_if i_m3 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m3[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM3),
  .hresp_in_from_slave(HRESPM3),

  // output ports
  .m_hsel(HSELM3),
  .m_haddr(HADDRM3),
  .m_htrans(HTRANSM3),
  .m_hwrite(HWRITEM3),
  .m_hsize(HSIZEM3),
  .m_hburst(HBURSTM3),
  .m_hprot(HPROTM3),
  .m_hready(HREADYMUXM3),
  .m_hwdata(HWDATAM3),
  
  .hready_out_from_slave(hready_from_m3),
  .hresp_from_slave(hresp_from_m3),
  .gnt(gnt_from_m3)

);


assign s_hresp_from_all_slave[4 * 2 - 1 : 3 * 2]   =  hresp_from_m3;
assign s_hready_from_all_slave[3]  = hready_from_m3;
assign s_hrdata_from_all_slave[4 * `AHB_DATA_WIDTH - 1 : 3 * `AHB_DATA_WIDTH]   = HRDATAM3;

assign req_2_m3 = { req_from_s15[3],  req_from_s14[3], req_from_s13[3], 
                    req_from_s12[3],  req_from_s11[3], req_from_s10[3], 
                    req_from_s9[3],   req_from_s8[3],  req_from_s7[3],
                    req_from_s6[3],   req_from_s5[3],  req_from_s4[3], 
                    req_from_s3[3],   req_from_s2[3],  req_from_s1[3], 
                    req_from_s0[3] };
`endif

`ifdef MASTER4
wire  hready_from_m4;
wire [1 : 0] hresp_from_m4;

assign     HMASTLOCKM4 = 0;
assign HMASTERM4 = 4'b0;


master_if i_m4 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m4[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM4),
  .hresp_in_from_slave(HRESPM4),

  // output ports
  .m_hsel(HSELM4),
  .m_haddr(HADDRM4),
  .m_htrans(HTRANSM4),
  .m_hwrite(HWRITEM4),
  .m_hsize(HSIZEM4),
  .m_hburst(HBURSTM4),
  .m_hprot(HPROTM4),
  .m_hready(HREADYMUXM4),
  .m_hwdata(HWDATAM4),
  
  .hready_out_from_slave(hready_from_m4),
  .hresp_from_slave(hresp_from_m4),
  .gnt(gnt_from_m4)

);


assign s_hresp_from_all_slave[5 * 2 - 1 : 4 * 2]   =  hresp_from_m4;
assign s_hready_from_all_slave[4]  = hready_from_m4;
assign s_hrdata_from_all_slave[5 * `AHB_DATA_WIDTH - 1 : 4 * `AHB_DATA_WIDTH]   = HRDATAM4;

assign req_2_m4 = { req_from_s15[4],  req_from_s14[4], req_from_s13[4], 
                    req_from_s12[4],  req_from_s11[4], req_from_s10[4], 
                    req_from_s9[4],   req_from_s8[4],  req_from_s7[4],
                    req_from_s6[4],   req_from_s5[4],  req_from_s4[4], 
                    req_from_s3[4],   req_from_s2[4],  req_from_s1[4], 
                    req_from_s0[4] };
`endif


`ifdef MASTER5
wire  hready_from_m5;
wire [1 : 0] hresp_from_m5;

assign     HMASTLOCKM5 = 0;
assign HMASTERM5 = 4'b0;


master_if i_m5 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m5[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM5),
  .hresp_in_from_slave(HRESPM5),

  // output ports
  .m_hsel(HSELM5),
  .m_haddr(HADDRM5),
  .m_htrans(HTRANSM5),
  .m_hwrite(HWRITEM5),
  .m_hsize(HSIZEM5),
  .m_hburst(HBURSTM5),
  .m_hprot(HPROTM5),
  .m_hready(HREADYMUXM5),
  .m_hwdata(HWDATAM5),
  
  .hready_out_from_slave(hready_from_m5),
  .hresp_from_slave(hresp_from_m5),
  .gnt(gnt_from_m5)

);


assign s_hresp_from_all_slave[6 * 2 - 1 : 5 * 2]   =  hresp_from_m5;
assign s_hready_from_all_slave[5]  = hready_from_m5;
assign s_hrdata_from_all_slave[6 * `AHB_DATA_WIDTH - 1 : 5 * `AHB_DATA_WIDTH]   = HRDATAM5;

assign req_2_m5 = { req_from_s15[5],  req_from_s14[5], req_from_s13[5], 
                    req_from_s12[5],  req_from_s11[5], req_from_s10[5], 
                    req_from_s9[5],   req_from_s8[5],  req_from_s7[5],
                    req_from_s6[5],   req_from_s5[5],  req_from_s4[5], 
                    req_from_s3[5],   req_from_s2[5],  req_from_s1[5], 
                    req_from_s0[5] };
`endif

`ifdef MASTER6
wire  hready_from_m6;
wire [1 : 0] hresp_from_m6;

assign     HMASTLOCKM6 = 0;
assign HMASTERM6 = 4'b0;


master_if i_m6 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m6[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM6),
  .hresp_in_from_slave(HRESPM6),

  // output ports
  .m_hsel(HSELM6),
  .m_haddr(HADDRM6),
  .m_htrans(HTRANSM6),
  .m_hwrite(HWRITEM6),
  .m_hsize(HSIZEM6),
  .m_hburst(HBURSTM6),
  .m_hprot(HPROTM6),
  .m_hready(HREADYMUXM6),
  .m_hwdata(HWDATAM6),
  
  .hready_out_from_slave(hready_from_m6),
  .hresp_from_slave(hresp_from_m6),
  .gnt(gnt_from_m6)

);


assign s_hresp_from_all_slave[7 * 2 - 1 : 6 * 2]   =  hresp_from_m6;
assign s_hready_from_all_slave[6]  = hready_from_m6;
assign s_hrdata_from_all_slave[7 * `AHB_DATA_WIDTH - 1 : 6 * `AHB_DATA_WIDTH]   = HRDATAM6;

assign req_2_m6 = { req_from_s15[6],  req_from_s14[6], req_from_s13[6], 
                    req_from_s12[6],  req_from_s11[6], req_from_s10[6], 
                    req_from_s9[6],   req_from_s8[6],  req_from_s7[6],
                    req_from_s6[6],   req_from_s5[6],  req_from_s4[6], 
                    req_from_s3[6],   req_from_s2[6],  req_from_s1[6], 
                    req_from_s0[6] };

`endif

`ifdef MASTER7
wire  hready_from_m7;
wire [1 : 0] hresp_from_m7;

assign     HMASTLOCKM7 = 0;
assign HMASTERM7 = 4'b0;


master_if i_m7 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m7[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM7),
  .hresp_in_from_slave(HRESPM7),

  // output ports
  .m_hsel(HSELM7),
  .m_haddr(HADDRM7),
  .m_htrans(HTRANSM7),
  .m_hwrite(HWRITEM7),
  .m_hsize(HSIZEM7),
  .m_hburst(HBURSTM7),
  .m_hprot(HPROTM7),
  .m_hready(HREADYMUXM7),
  .m_hwdata(HWDATAM7),
  
  .hready_out_from_slave(hready_from_m7),
  .hresp_from_slave(hresp_from_m7),
  .gnt(gnt_from_m7)

);


assign s_hresp_from_all_slave[8 * 2 - 1 : 7 * 2]   =  hresp_from_m7;
assign s_hready_from_all_slave[7]  = hready_from_m7;
assign s_hrdata_from_all_slave[8 * `AHB_DATA_WIDTH - 1 : 7 * `AHB_DATA_WIDTH]   = HRDATAM7;

assign req_2_m7 = { req_from_s15[7],  req_from_s14[7], req_from_s13[7], 
                    req_from_s12[7],  req_from_s11[7], req_from_s10[7], 
                    req_from_s9[7],   req_from_s8[7],  req_from_s7[7],
                    req_from_s6[7],   req_from_s5[7],  req_from_s4[7], 
                    req_from_s3[7],   req_from_s2[7],  req_from_s1[7], 
                    req_from_s0[7] };
`endif


`ifdef MASTER8
wire  hready_from_m8;
wire [1 : 0] hresp_from_m8;

assign     HMASTLOCKM8 = 0;
assign HMASTERM8 = 4'b0;


master_if i_m8 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m8[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM8),
  .hresp_in_from_slave(HRESPM8),

  // output ports
  .m_hsel(HSELM8),
  .m_haddr(HADDRM8),
  .m_htrans(HTRANSM8),
  .m_hwrite(HWRITEM8),
  .m_hsize(HSIZEM8),
  .m_hburst(HBURSTM8),
  .m_hprot(HPROTM8),
  .m_hready(HREADYMUXM8),
  .m_hwdata(HWDATAM8),
  
  .hready_out_from_slave(hready_from_m8),
  .hresp_from_slave(hresp_from_m8),
  .gnt(gnt_from_m8)

);


assign s_hresp_from_all_slave[9 * 2 - 1 : 8 * 2]   =  hresp_from_m8;
assign s_hready_from_all_slave[8]  = hready_from_m8;
assign s_hrdata_from_all_slave[9 * `AHB_DATA_WIDTH - 1 : 8 * `AHB_DATA_WIDTH]   = HRDATAM8;

assign req_2_m8 = { req_from_s15[8],  req_from_s14[8], req_from_s13[8], 
                    req_from_s12[8],  req_from_s11[8], req_from_s10[8], 
                    req_from_s9[8],   req_from_s8[8],  req_from_s7[8],
                    req_from_s6[8],   req_from_s5[8],  req_from_s4[8], 
                    req_from_s3[8],   req_from_s2[8],  req_from_s1[8], 
                    req_from_s0[8] };
`endif

`ifdef MASTER9
wire  hready_from_m9;
wire [1 : 0] hresp_from_m9;

assign     HMASTLOCKM9 = 0;
assign HMASTERM9 = 4'b0;


master_if i_m9 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m9[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM9),
  .hresp_in_from_slave(HRESPM9),

  // output ports
  .m_hsel(HSELM9),
  .m_haddr(HADDRM9),
  .m_htrans(HTRANSM9),
  .m_hwrite(HWRITEM9),
  .m_hsize(HSIZEM9),
  .m_hburst(HBURSTM9),
  .m_hprot(HPROTM9),
  .m_hready(HREADYMUXM9),
  .m_hwdata(HWDATAM9),
  
  .hready_out_from_slave(hready_from_m9),
  .hresp_from_slave(hresp_from_m9),
  .gnt(gnt_from_m9)

);


assign s_hresp_from_all_slave[10 * 2 - 1 : 9 * 2]   =  hresp_from_m9;
assign s_hready_from_all_slave[9]  = hready_from_m9;
assign s_hrdata_from_all_slave[10 * `AHB_DATA_WIDTH - 1 : 9 * `AHB_DATA_WIDTH]   = HRDATAM9;

assign req_2_m9 = { req_from_s15[9],  req_from_s14[9], req_from_s13[9], 
                    req_from_s12[9],  req_from_s11[9], req_from_s10[9], 
                    req_from_s9[9],   req_from_s8[9],  req_from_s7[9],
                    req_from_s6[9],   req_from_s5[9],  req_from_s4[9], 
                    req_from_s3[9],   req_from_s2[9],  req_from_s1[9], 
                    req_from_s0[9] };
`endif

`ifdef MASTER10
wire  hready_from_m10;
wire [1 : 0] hresp_from_m10;

assign     HMASTLOCKM10 = 0;
assign HMASTERM10 = 4'b0;


master_if i_m10 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m10[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM10),
  .hresp_in_from_slave(HRESPM10),

  // output ports
  .m_hsel(HSELM10),
  .m_haddr(HADDRM10),
  .m_htrans(HTRANSM10),
  .m_hwrite(HWRITEM10),
  .m_hsize(HSIZEM10),
  .m_hburst(HBURSTM10),
  .m_hprot(HPROTM10),
  .m_hready(HREADYMUXM10),
  .m_hwdata(HWDATAM10),
  
  .hready_out_from_slave(hready_from_m10),
  .hresp_from_slave(hresp_from_m10),
  .gnt(gnt_from_m10)

);


assign s_hresp_from_all_slave[11 * 2 - 1 : 10 * 2]   =  hresp_from_m10;
assign s_hready_from_all_slave[10]  = hready_from_m10;
assign s_hrdata_from_all_slave[11 * `AHB_DATA_WIDTH - 1 : 10 * `AHB_DATA_WIDTH]   = HRDATAM10;

assign req_2_m10 = { req_from_s15[10],  req_from_s14[10], req_from_s13[10], 
                     req_from_s12[10],  req_from_s11[10], req_from_s10[10], 
                     req_from_s9[10],   req_from_s8[10],  req_from_s7[10],
                     req_from_s6[10],   req_from_s5[10],  req_from_s4[10], 
                     req_from_s3[10],   req_from_s2[10],  req_from_s1[10], 
                     req_from_s0[10] };
`endif

`ifdef MASTER11
wire  hready_from_m11;
wire [1 : 0] hresp_from_m11;

assign     HMASTLOCKM11 = 0;
assign HMASTERM11 = 4'b0;

master_if i_m11 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m11[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM11),
  .hresp_in_from_slave(HRESPM11),

  // output ports
  .m_hsel(HSELM11),
  .m_haddr(HADDRM11),
  .m_htrans(HTRANSM11),
  .m_hwrite(HWRITEM11),
  .m_hsize(HSIZEM11),
  .m_hburst(HBURSTM11),
  .m_hprot(HPROTM11),
  .m_hready(HREADYMUXM11),
  .m_hwdata(HWDATAM11),
  
  .hready_out_from_slave(hready_from_m11),
  .hresp_from_slave(hresp_from_m11),
  .gnt(gnt_from_m11)

);


assign s_hresp_from_all_slave[12 * 2 - 1 : 11 * 2]   =  hresp_from_m11;
assign s_hready_from_all_slave[11]  = hready_from_m11;
assign s_hrdata_from_all_slave[12 * `AHB_DATA_WIDTH - 1 : 11 * `AHB_DATA_WIDTH]   = HRDATAM11;

assign req_2_m11 = { req_from_s15[11],  req_from_s14[11], req_from_s13[11], 
                     req_from_s12[11],  req_from_s11[11], req_from_s10[11], 
                     req_from_s9[11],   req_from_s8[11],  req_from_s7[11],
                     req_from_s6[11],   req_from_s5[11],  req_from_s4[11], 
                     req_from_s3[11],   req_from_s2[11],  req_from_s1[11], 
                     req_from_s0[11] };

`endif

`ifdef MASTER12
wire  hready_from_m12;
wire [1 : 0] hresp_from_m12;

assign     HMASTLOCKM12 = 0;
assign HMASTERM12 = 4'b0;


master_if i_m12 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m12[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM12),
  .hresp_in_from_slave(HRESPM12),

  // output ports
  .m_hsel(HSELM12),
  .m_haddr(HADDRM12),
  .m_htrans(HTRANSM12),
  .m_hwrite(HWRITEM12),
  .m_hsize(HSIZEM12),
  .m_hburst(HBURSTM12),
  .m_hprot(HPROTM12),
  .m_hready(HREADYMUXM12),
  .m_hwdata(HWDATAM12),
  
  .hready_out_from_slave(hready_from_m12),
  .hresp_from_slave(hresp_from_m12),
  .gnt(gnt_from_m12)

);


assign s_hresp_from_all_slave[13 * 2 - 1 : 12 * 2]   =  hresp_from_m12;
assign s_hready_from_all_slave[12]  = hready_from_m12;
assign s_hrdata_from_all_slave[13 * `AHB_DATA_WIDTH - 1 : 12 * `AHB_DATA_WIDTH]   = HRDATAM12;

assign req_2_m12 = { req_from_s15[12],  req_from_s14[12], req_from_s13[12], 
                     req_from_s12[12],  req_from_s11[12], req_from_s10[12], 
                     req_from_s9[12],   req_from_s8[12],  req_from_s7[12],
                     req_from_s6[12],   req_from_s5[12],  req_from_s4[12], 
                     req_from_s3[12],   req_from_s2[12],  req_from_s1[12], 
                     req_from_s0[12] };
`endif

`ifdef MASTER13
wire  hready_from_m13;
wire [1 : 0] hresp_from_m13;

assign     HMASTLOCKM13 = 0;
assign HMASTERM13 = 4'b0;



master_if i_m13 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m13[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM13),
  .hresp_in_from_slave(HRESPM13),

  // output ports
  .m_hsel(HSELM13),
  .m_haddr(HADDRM13),
  .m_htrans(HTRANSM13),
  .m_hwrite(HWRITEM13),
  .m_hsize(HSIZEM13),
  .m_hburst(HBURSTM13),
  .m_hprot(HPROTM13),
  .m_hready(HREADYMUXM13),
  .m_hwdata(HWDATAM13),
  
  .hready_out_from_slave(hready_from_m13),
  .hresp_from_slave(hresp_from_m13),
  .gnt(gnt_from_m13)

);


assign s_hresp_from_all_slave[14 * 2 - 1 : 13 * 2]   =  hresp_from_m13;
assign s_hready_from_all_slave[13]  = hready_from_m13;
assign s_hrdata_from_all_slave[14 * `AHB_DATA_WIDTH - 1 : 13 * `AHB_DATA_WIDTH]   = HRDATAM13;

assign req_2_m13 = { req_from_s15[13],  req_from_s14[13], req_from_s13[13], 
                     req_from_s12[13],  req_from_s11[13], req_from_s10[13], 
                     req_from_s9[13],   req_from_s8[13],  req_from_s7[13],
                     req_from_s6[13],   req_from_s5[13],  req_from_s4[13], 
                     req_from_s3[13],   req_from_s2[13],  req_from_s1[13], 
                     req_from_s0[13] };

`endif

`ifdef MASTER14
wire  hready_from_m14;
wire [1 : 0] hresp_from_m14;

assign     HMASTLOCKM14 = 0;
assign HMASTERM14 = 4'b0;


master_if i_m14 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m14[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM14),
  .hresp_in_from_slave(HRESPM14),

  // output ports
  .m_hsel(HSELM14),
  .m_haddr(HADDRM14),
  .m_htrans(HTRANSM14),
  .m_hwrite(HWRITEM14),
  .m_hsize(HSIZEM14),
  .m_hburst(HBURSTM14),
  .m_hprot(HPROTM14),
  .m_hready(HREADYMUXM14),
  .m_hwdata(HWDATAM14),
  
  .hready_out_from_slave(hready_from_m14),
  .hresp_from_slave(hresp_from_m14),
  .gnt(gnt_from_m14)

);


assign s_hresp_from_all_slave[15 * 2 - 1 : 14 * 2]   =  hresp_from_m14;
assign s_hready_from_all_slave[14]  = hready_from_m14;
assign s_hrdata_from_all_slave[15 * `AHB_DATA_WIDTH - 1 : 14 * `AHB_DATA_WIDTH]   = HRDATAM14;

assign req_2_m14 = { req_from_s15[14],  req_from_s14[14], req_from_s13[14], 
                     req_from_s12[14],  req_from_s11[14], req_from_s10[14], 
                     req_from_s9[14],   req_from_s8[14],  req_from_s7[14],
                     req_from_s6[14],   req_from_s5[14],  req_from_s4[14], 
                     req_from_s3[14],   req_from_s2[14],  req_from_s1[14], 
                     req_from_s0[14] };
`endif

`ifdef MASTER15
wire  hready_from_m15;
wire [1 : 0] hresp_from_m15;

assign     HMASTLOCKM15 = 0;
assign HMASTERM15 = 4'b0;


master_if i_m15 (

  // input ports
  .hclk(HCLK),
  .hresetn(HRESETn),
  .s_haddr(haddr_2_master_if),
  .s_htrans(htran_2_master_if),
  .s_hwrite(hwrite_2_master_if),
  .s_hsize(hsize_2_master_if),
  .s_hburst(hburst_2_master_if),
  .s_hprot(hprot_2_master_if),
  .s_hready(hready_2_master_if),
  .s_req(req_2_m15[`NUM_OF_SLAVES - 1 : 0]),
  .s_hwdata(hwdata_2_master_if),
  
  .hready_in_from_slave(HREADYOUTM15),
  .hresp_in_from_slave(HRESPM15),

  // output ports
  .m_hsel(HSELM15),
  .m_haddr(HADDRM15),
  .m_htrans(HTRANSM15),
  .m_hwrite(HWRITEM15),
  .m_hsize(HSIZEM15),
  .m_hburst(HBURSTM15),
  .m_hprot(HPROTM15),
  .m_hready(HREADYMUXM15),
  .m_hwdata(HWDATAM15),
  
  .hready_out_from_slave(hready_from_m15),
  .hresp_from_slave(hresp_from_m15),
  .gnt(gnt_from_m15)

);


assign s_hresp_from_all_slave[16 * 2 - 1 : 15 * 2]   =  hresp_from_m15;
assign s_hready_from_all_slave[15]  = hready_from_m15;
assign s_hrdata_from_all_slave[16 * `AHB_DATA_WIDTH - 1 : 15 * `AHB_DATA_WIDTH]   = HRDATAM15;

assign req_2_m15 = { req_from_s15[15],  req_from_s14[15], req_from_s13[15], 
                     req_from_s12[15],  req_from_s11[15], req_from_s10[15], 
                     req_from_s9[15],   req_from_s8[15],  req_from_s7[15],
                     req_from_s6[15],   req_from_s5[15],  req_from_s4[15], 
                     req_from_s3[15],   req_from_s2[15],  req_from_s1[15], 
                     req_from_s0[15] };

`endif

// Master Instantiation done


endmodule
