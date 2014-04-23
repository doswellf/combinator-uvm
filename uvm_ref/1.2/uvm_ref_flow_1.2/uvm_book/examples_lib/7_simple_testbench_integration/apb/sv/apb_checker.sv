/*******************************************************************************

  FILE : apb_checker.sv

  This file includes all the implementation files needed to use the apb. 

*******************************************************************************/
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



`ifdef ABV_OFF
 // compiler directive, Use +define+ABV_OFF or -define ABV_OFF.
`else  // Checking on by default

   //----------------------
   // Initialize simulation
   //----------------------
      initial
      begin
         // Format for time reporting
         //$timeformat(-9, 2, " ns", 10);
         $display("CHECKER_APB_INFO: Running checker_apb (SVA implementation)");
      end

   //-------------------------------------------
   // Internal signals for data integrity checks
   //-------------------------------------------
      logic  [PADDR_WIDTH-1:0]  paddr_sv;
      logic                     pwrite_s;
      logic  [PWDATA_WIDTH-1:0] pwdata_sv;
      logic  [PRDATA_WIDTH-1:0] prdata_sv;

      assign paddr_sv  = paddr;
      assign pwrite_s  = prwd; //pwrite
      assign pwdata_sv = pwdata;
      assign prdata_sv = prdata;

   //----------------------------------------------
   // Internal signals for APB operational activity
   //----------------------------------------------
      `define IDLE   (!psel & !penable)
      `define SETUP  ( psel & !penable)
      `define ENABLE ( psel &  penable)

   //<<<<<<<<<<<<<<<<<<<<<<
   // PROTOCOL_CHECKS_BEGIN
   //<<<<<<<<<<<<<<<<<<<<<<

      // Rule : IDLE - the default state for the peripheral bus.
      property p_001_master_idle_on_reset;
         @(posedge pclock)
            not (!preset && !(`IDLE));
      endproperty

   assert_001_master_idle_on_reset : assert property (p_001_master_idle_on_reset);     

      // Rule : State diagram does not allow PENABLE=1 with PSELx=0 //only valid in single psel systems !
      property p_002_master_never_penable_without_psel; 
         @(posedge pclock)                         
            not (!psel && penable);           
      endproperty 

       //only valid in single psel systems 
      assert_002_master_never_penable_without_psel : assert property (p_002_master_never_penable_without_psel);
      // Rule : IDLE - When a transfer is required the bus moves into the SETUP state, where the appropriate PSELx is asserted.
      property p_003_master_state_idle_then_idle_or_setup;
         @(posedge pclock) disable iff (!preset)
            (!psel |=> !penable);
      endproperty

      assert_003_master_state_idle_then_idle_or_setup : assert property (p_003_master_state_idle_then_idle_or_setup);

      // Rule : SETUP - The bus only remains in the SETUP state for one clock cycle and will always move to the ENABLE state on the next rising edge of the clock.
      property p_004_master_state_setup_then_access_on_next_cycle;
         @(posedge pclock) disable iff (!preset)
            ((`SETUP) |=> (`ENABLE));
      endproperty

      assert_004_master_state_setup_then_access_on_next_cycle : assert property (p_004_master_state_setup_then_access_on_next_cycle);


      // Rule : The address, write and select signals all remain stable during the transition from the SETUP to ENABLE state."
      // NOTE : psel stablity is already covered by master_state_setup_then_access_on_next_cycle
      property p_006_master_state_paddr_stable_between_setup_and_access;
         @(posedge pclock) disable iff (!preset)
            ((`SETUP) |=> $stable(paddr));
      endproperty

      assert_006_master_state_paddr_stable_between_setup_and_access : assert property (p_006_master_state_paddr_stable_between_setup_and_access);

      property p_007_master_state_pwrite_stable_between_setup_and_access;
         @(posedge pclock) disable iff (!preset)
            ((`SETUP) |=> $stable(prwd));
      endproperty

      assert_007_master_state_pwrite_stable_between_setup_and_access : assert property (p_007_master_state_pwrite_stable_between_setup_and_access);

      // Rule : The write transfer starts with the address, write data and write signals,
      //        The address, data and control signals all remaing valid throughout the ENABLE cycle. The transfer completes at the end of this cycle.
      property p_008_master_pwdata_stable_throughout_access;
         @(posedge pclock) disable iff (!preset)
            (((`SETUP) && prwd) || ((`ENABLE) && prwd && !pready) |=> $stable(pwdata));
      endproperty

      assert_008_master_pwdata_stable_throughout_access : assert property (p_008_master_pwdata_stable_throughout_access);

      // Validity of APB signals during transfers : Another way to check X on the bus

      // Rule : Write transfer - The write transfer starts with the
      //        address, write data and write signals all changing after the
      //        rising edge of the clock. The address, data and write
      //        signals remain valid throughout the ENABLE cycle. The
      //        transfer completes at the end of this cycle."
      property p_009_master_paddr_valid_throughout_access_cycle;
         @(posedge pclock) disable iff (!preset)
            (psel |-> (!(paddr ^ paddr_sv)));
      endproperty

      assert_009_master_paddr_valid_throughout_access_cycle : assert property (p_009_master_paddr_valid_throughout_access_cycle);

      property p_010_master_pwrite_valid_throughout_access_cycle;
         @(posedge pclock) disable iff (!preset)
            (psel |-> (!(prwd ^ pwrite_s)));
      endproperty

      assert_010_master_pwrite_valid_throughout_access_cycle : assert property (p_010_master_pwrite_valid_throughout_access_cycle);

      property p_011_master_pwdata_valid_throughout_access_cycle;
         @(posedge pclock) disable iff (!preset)
            ((psel & prwd) |-> (!(pwdata ^ pwdata_sv)));
      endproperty

      assert_011_master_pwdata_valid_throughout_access_cycle : assert property (p_011_master_pwdata_valid_throughout_access_cycle);


      // Rule : Read transfer -
      //        "In the case of a read, the slave must provide the data during the
      //        ENABLE cycle. The data is sampled on the rising edge of the clock
      //        at the end of the ENABLE cycle."

      property p_012_slave_prdata_valid_on_access_cycle; // Valid for APB Version-2.0
         @(posedge pclock) disable iff (!preset)
            ((psel & !prwd & penable) |-> (!(prdata ^ prdata_sv)));
      endproperty

      assert_012_slave_prdata_valid_on_access_cycle : assert property (p_012_slave_prdata_valid_on_access_cycle);


   //>>>>>>>>>>>>>>>>>>>>
   // PROTOCOL_CHECKS_END
   //>>>>>>>>>>>>>>>>>>>>

   //<<<<<<<<<<<<<<<<<<<<<<
   // COVERAGE_CHECKS_BEGIN
   //<<<<<<<<<<<<<<<<<<<<<<

   `ifdef COVERAGE_OFF // compiler directive, Use +define+COVERAGE_OFF or -define COVERAGE_OFF.
   `else  // Checking on by default
      cover_101_wr_transfer_with_no_wait : cover property (@(posedge pclock) disable iff (!preset) (`IDLE) ##1 ((`SETUP) & prwd) ##1 (`ENABLE));
      cover_102_wr_transfer_with_wait    : cover property (@(posedge pclock) disable iff (!preset) (`IDLE) ##1 ((`SETUP) & prwd) ##[1:$] (`ENABLE));
      cover_103_rd_transfer_with_no_wait : cover property (@(posedge pclock) disable iff (!preset) (`IDLE) ##1 ((`SETUP) & !prwd) ##1 (`ENABLE));
      cover_104_rd_transfer_with_wait    : cover property (@(posedge pclock) disable iff (!preset) (`IDLE) ##1 ((`SETUP) & !prwd) ##[1:$] (`ENABLE));
      cover_105_consecutive_transfer     : cover property (@(posedge pclock) disable iff (!preset) (`ENABLE) ##1 (`SETUP) ##1 (`ENABLE));
      cover_106_end_transfer             : cover property (@(posedge pclock) disable iff (!preset) (`ENABLE) ##1 (`IDLE));
   `endif // COVERAGE_OFF

   //>>>>>>>>>>>>>>>>>>>>
   // COVERAGE_CHECKS_END
   //>>>>>>>>>>>>>>>>>>>>

   //<<<<<<<<<<<<<<<<<<<<
   // SANITY_CHECKS_BEGIN
   //<<<<<<<<<<<<<<<<<<<<

   `ifdef SANITY_OFF // compiler directive, Use +define+SANITY_OFF or -define SANITY_OFF .
   `else  // Checking on by default
      cover_201_psel_goes_high    : cover property (@(posedge pclock) disable iff (!preset) (!psel ##1 psel));
      cover_202_psel_goes_low     : cover property (@(posedge pclock) disable iff (!preset) (psel ##1 !psel));
      cover_203_penable_goes_high : cover property (@(posedge pclock) disable iff (!preset) (!penable ##1 penable));
      cover_204_penable_goes_low  : cover property (@(posedge pclock) disable iff (!preset) (penable ##1 !penable));
      cover_205_pwrite_goes_high  : cover property (@(posedge pclock) disable iff (!preset) (!prwd ##1 prwd));
      cover_206_pwrite_goes_low   : cover property (@(posedge pclock) disable iff (!preset) (prwd ##1 !prwd));
   `endif // SANITY_OFF

   //>>>>>>>>>>>>>>>>>>
   // SANITY_CHECKS_END
   //>>>>>>>>>>>>>>>>>>

`endif // ABV_OFF
