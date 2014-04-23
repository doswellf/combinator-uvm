/*-------------------------------------------------------------------------
File name   : apb_subsystem_vir_seq_lib.sv
Title       : Virtual Sequence
Project     :
Created     :
Description : This file implements the virtual sequence for the APB-UART env.
Notes       : The concurrent_u2a_a2u_rand_trans sequence first configures
            : the UART RTL. Once the configuration sequence is completed
            : random read/write sequences from both the UVCs are enabled
            : in parallel. At the end a Rx FIFO read sequence is executed.
            : The intrpt_seq needs to be modified to take interrupt into account.
----------------------------------------------------------------------*/
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


`ifndef APB_UART_VIRTUAL_SEQ_LIB_SV
`define APB_UART_VIRTUAL_SEQ_LIB_SV

class u2a_incr_payload extends uvm_sequence;

  //bit success;
  rand int unsigned num_u02a_wr;
  rand int unsigned num_a2u0_wr;
  rand int unsigned num_u12a_wr;
  rand int unsigned num_a2u1_wr;

  function new(string name="u2a_incr_payload",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(u2a_incr_payload)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  constraint num_u02a_wr_ct {(num_u02a_wr > 2) && (num_u02a_wr <= 4);}
  constraint num_a2u0_wr_ct {(num_a2u0_wr == 1);}
  constraint num_u12a_wr_ct {(num_u12a_wr > 2) && (num_u12a_wr <= 4);}
  constraint num_a2u1_wr_ct {(num_a2u1_wr == 1);}

  // APB and UART UVC sequences
  uart_ctrl_config_reg_seq uart_cfg_dut_seq;
  uart_incr_payload_seq uart_seq;
  intrpt_seq rd_rx_fifo;
  ahb_to_uart_wr raw_seq;

  virtual task body();
    uvm_test_done.raise_objection(this);

    `uvm_info("vseq", $sformatf("Number of APB->UART0 Transaction = %d", num_a2u0_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Number of APB->UART1 Transaction = %d", num_a2u1_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Number of UART0->APB Transaction = %d", num_u02a_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Number of UART1->APB Transaction = %d", num_u12a_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Total Number of AHB, UART Transaction = %d", num_u02a_wr + num_a2u0_wr + num_u02a_wr + num_a2u0_wr), UVM_LOW)

    // configure UART0 DUT
    uart_cfg_dut_seq = uart_ctrl_config_reg_seq::type_id::create("uart_cfg_dut_seq");
    uart_cfg_dut_seq.reg_model = p_sequencer.reg_model_ptr.uart0_rm;
    uart_cfg_dut_seq.start(null);


    // configure UART1 DUT
    uart_cfg_dut_seq = uart_ctrl_config_reg_seq::type_id::create("uart_cfg_dut_seq");
    uart_cfg_dut_seq.reg_model = p_sequencer.reg_model_ptr.uart1_rm;
    uart_cfg_dut_seq.start(null);


    #1000;
    fork
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u0_wr; base_addr == 'h810000;})
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u1_wr; base_addr == 'h880000;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart0_seqr, {cnt == num_u02a_wr;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart1_seqr, {cnt == num_u12a_wr;})
    join
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u02a_wr; base_addr == 'h810000;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u12a_wr; base_addr == 'h880000;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : u2a_incr_payload

// rand shutdown and power-on
class on_off_seq extends uvm_sequence;
  `uvm_object_utils(on_off_seq)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)

  function new(string name = "on_off_seq");
     super.new(name);
  endfunction

  shutdown_dut shut_dut;
  poweron_dut power_dut;

  virtual task body();
    uvm_test_done.raise_objection(this);
    for (int i=0 ; i <= 10; i ++) begin
      `uvm_do_on(shut_dut, p_sequencer.ahb_seqr)
       #4000;
      `uvm_do_on(power_dut, p_sequencer.ahb_seqr)
       #4000;
    end
    uvm_test_done.drop_objection(this);
  endtask : body
  
endclass : on_off_seq


// shutdown and power-on for uart1
class on_off_uart1_seq extends uvm_sequence;
  `uvm_object_utils(on_off_uart1_seq)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)

  function new(string name = "on_off_uart1_seq");
     super.new(name);
  endfunction

  shutdown_dut shut_dut;
  poweron_dut power_dut;

  virtual task body();
    uvm_test_done.raise_objection(this);
    for (int i=0 ; i <= 5; i ++) begin
      `uvm_do_on_with(shut_dut, p_sequencer.ahb_seqr, {write_data == 1;})
        #4000;
      `uvm_do_on(power_dut, p_sequencer.ahb_seqr)
        #4000;
    end
    uvm_test_done.drop_objection(this);
  endtask : body
  
endclass : on_off_uart1_seq

// lp seq, configuration sequence
class lp_shutdown_config extends uvm_sequence;

  //bit success;
  rand int unsigned num_u02a_wr;
  rand int unsigned num_a2u0_wr;
  rand int unsigned num_u12a_wr;
  rand int unsigned num_a2u1_wr;

  function new(string name="lp_shutdown_config",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(lp_shutdown_config)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  constraint num_u02a_wr_ct {(num_u02a_wr > 2) && (num_u02a_wr <= 4);}
  constraint num_a2u0_wr_ct {(num_a2u0_wr == 1);}
  constraint num_u12a_wr_ct {(num_u12a_wr > 2) && (num_u12a_wr <= 4);}
  constraint num_a2u1_wr_ct {(num_a2u1_wr == 1);}

  // APB and UART UVC sequences
  uart_ctrl_config_reg_seq uart_cfg_dut_seq;
  uart_incr_payload_seq uart_seq;
  intrpt_seq rd_rx_fifo;
  ahb_to_uart_wr raw_seq;

  virtual task body();
    uvm_test_done.raise_objection(this);

    `uvm_info("vseq", $sformatf("Number of APB->UART0 Transaction = %d", num_a2u0_wr), UVM_LOW);
    `uvm_info("vseq", $sformatf("Number of APB->UART1 Transaction = %d", num_a2u1_wr), UVM_LOW);
    `uvm_info("vseq", $sformatf("Number of UART0->APB Transaction = %d", num_u02a_wr), UVM_LOW);
    `uvm_info("vseq", $sformatf("Number of UART1->APB Transaction = %d", num_u12a_wr), UVM_LOW);
    `uvm_info("vseq", $sformatf("Total Number of AHB, UART Transaction = %d", num_u02a_wr + num_a2u0_wr + num_u02a_wr + num_a2u0_wr), UVM_LOW);

    // configure UART0 DUT
    uart_cfg_dut_seq = uart_ctrl_config_reg_seq::type_id::create("uart_cfg_dut_seq");
    uart_cfg_dut_seq.reg_model = p_sequencer.reg_model_ptr.uart0_rm;
    uart_cfg_dut_seq.start(null);


    // configure UART1 DUT
    uart_cfg_dut_seq = uart_ctrl_config_reg_seq::type_id::create("uart_cfg_dut_seq");
    uart_cfg_dut_seq.reg_model = p_sequencer.reg_model_ptr.uart1_rm;
    uart_cfg_dut_seq.start(null);


    #1000;
    fork
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u0_wr; base_addr == 'h810000;})
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u1_wr; base_addr == 'h880000;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart0_seqr, {cnt == num_u02a_wr;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart1_seqr, {cnt == num_u12a_wr;})
    join
    #1000;
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u02a_wr; base_addr == 'h810000;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u12a_wr; base_addr == 'h880000;})


    fork
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u0_wr; base_addr == 'h810000;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart0_seqr, {cnt == num_u02a_wr;})
    join_none

    uvm_test_done.drop_objection(this);
  endtask : body
endclass : lp_shutdown_config

// rand lp shutdown seq between uart 1 and smc
class lp_shutdown_rand extends uvm_sequence;

  rand int unsigned num_u02a_wr;
  rand int unsigned num_a2u0_wr;
  rand int unsigned num_u12a_wr;
  rand int unsigned num_a2u1_wr;

  function new(string name="lp_shutdown_rand",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(lp_shutdown_rand)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  constraint num_u02a_wr_ct {(num_u02a_wr > 2) && (num_u02a_wr <= 4);}
  constraint num_a2u0_wr_ct {(num_a2u0_wr == 1);}
  constraint num_u12a_wr_ct {(num_u12a_wr > 2) && (num_u12a_wr <= 4);}
  constraint num_a2u1_wr_ct {(num_a2u1_wr == 1);}


  on_off_seq on_off_seq;
  uart_incr_payload_seq uart_seq;
  intrpt_seq rd_rx_fifo;
  ahb_to_uart_wr raw_seq;
  lp_shutdown_config lp_shutdown_config;

  virtual task body();
    uvm_test_done.raise_objection(this);

    // call the shut down seq
    `uvm_do(lp_shutdown_config);
    #20000;
    `uvm_do(on_off_seq);

    #10000;
    fork
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u1_wr; base_addr == 'h880000;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart1_seqr, {cnt == num_u12a_wr;})
    join
    #1000;
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u02a_wr; base_addr == 'h810000;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u12a_wr; base_addr == 'h880000;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : lp_shutdown_rand


// sequence for shutting down uart 1 alone
class lp_shutdown_uart1 extends uvm_sequence;

  rand int unsigned num_u02a_wr;
  rand int unsigned num_a2u0_wr;
  rand int unsigned num_u12a_wr;
  rand int unsigned num_a2u1_wr;

  function new(string name="lp_shutdown_uart1",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(lp_shutdown_uart1)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  constraint num_u02a_wr_ct {(num_u02a_wr > 2) && (num_u02a_wr <= 4);}
  constraint num_a2u0_wr_ct {(num_a2u0_wr == 1);}
  constraint num_u12a_wr_ct {(num_u12a_wr > 2) && (num_u12a_wr <= 4);}
  constraint num_a2u1_wr_ct {(num_a2u1_wr == 2);}


  on_off_uart1_seq on_off_uart1_seq;
  uart_incr_payload_seq uart_seq;
  intrpt_seq rd_rx_fifo;
  ahb_to_uart_wr raw_seq;
  lp_shutdown_config lp_shutdown_config;

  virtual task body();
    uvm_test_done.raise_objection(this);

    // call the shut down seq
    `uvm_do(lp_shutdown_config);
    #20000;
    `uvm_do(on_off_uart1_seq);

    #10000;
    fork
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == num_a2u1_wr; base_addr == 'h880000;})
      `uvm_do_on_with(uart_seq, p_sequencer.uart1_seqr, {cnt == num_u12a_wr;})
    join
    #1000;
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u02a_wr; base_addr == 'h810000;})
    `uvm_do_on_with(rd_rx_fifo, p_sequencer.ahb_seqr, {num_of_rd == num_u12a_wr; base_addr == 'h880000;})

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : lp_shutdown_uart1



class apb_spi_incr_payload extends uvm_sequence;

  rand int unsigned num_spi2a_wr;
  rand int unsigned num_a2spi_wr;

  function new(string name="apb_spi_incr_payload",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(apb_spi_incr_payload)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  constraint num_spi2a_wr_ct {(num_spi2a_wr > 2) && (num_spi2a_wr <= 4);}
  constraint num_a2spi_wr_ct {(num_a2spi_wr == 4);}

  // APB and UART UVC sequences
  spi_cfg_reg_seq spi_cfg_dut_seq;
  spi_incr_payload spi_seq;
  read_spi_rx_reg rd_rx_reg;
  ahb_to_spi_wr raw_seq;
  spi_en_tx_reg_seq en_spi_tx_seq;

  virtual task body();
    uvm_test_done.raise_objection(this);

    `uvm_info("vseq", $sformatf("Number of APB->SPI Transaction = %d", num_a2spi_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Number of SPI->APB Transaction = %d", num_a2spi_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Total Number of AHB, SPI Transaction = %d", 2 * num_a2spi_wr), UVM_LOW)

    // configure SPI DUT
    spi_cfg_dut_seq = spi_cfg_reg_seq::type_id::create("spi_cfg_dut_seq");
    spi_cfg_dut_seq.reg_model = p_sequencer.reg_model_ptr.spi_rf;
    spi_cfg_dut_seq.start(null);


    for (int i = 0; i < num_a2spi_wr; i++) begin
      fork
        begin
            `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {num_of_wr == 1; base_addr == 'h800000;})
            en_spi_tx_seq = spi_en_tx_reg_seq::type_id::create("en_spi_tx_seq");
            en_spi_tx_seq.reg_model = p_sequencer.reg_model_ptr.spi_rf;
            en_spi_tx_seq.start(null);
            #10000;
        end
        begin
           `uvm_do_on_with(spi_seq, p_sequencer.spi0_seqr, {cnt_i == 1;})
            #10000;
           `uvm_do_on_with(rd_rx_reg, p_sequencer.ahb_seqr, {num_of_rd == 1; base_addr == 'h800000;})
        end
      join
    end

    #1000;
    uvm_test_done.drop_objection(this);
  endtask : body

endclass : apb_spi_incr_payload

class apb_gpio_simple_vseq extends uvm_sequence;

  rand int unsigned num_a2gpio_wr;

  function new(string name="apb_gpio_simple_vseq",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(apb_gpio_simple_vseq)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  constraint num_a2gpio_wr_ct {(num_a2gpio_wr == 4);}

  // APB and UART UVC sequences
  gpio_cfg_reg_seq gpio_cfg_dut_seq;
  gpio_simple_trans_seq gpio_seq;
  read_gpio_rx_reg rd_rx_reg;
  ahb_to_gpio_wr raw_seq;

  virtual task body();
    uvm_test_done.raise_objection(this);

    `uvm_info("vseq", $sformatf("Number of AHB->GPIO Transaction = %d", num_a2gpio_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Number of GPIO->APB Transaction = %d", num_a2gpio_wr), UVM_LOW)
    `uvm_info("vseq", $sformatf("Total Number of AHB, GPIO Transaction = %d", 2 * num_a2gpio_wr), UVM_LOW)

    // configure SPI DUT
    gpio_cfg_dut_seq = gpio_cfg_reg_seq::type_id::create("gpio_cfg_dut_seq");
    gpio_cfg_dut_seq.reg_model = p_sequencer.reg_model_ptr.gpio_rf;
    gpio_cfg_dut_seq.start(null);


    for (int i = 0; i < num_a2gpio_wr; i++) begin
      `uvm_do_on_with(raw_seq, p_sequencer.ahb_seqr, {base_addr == 'h820000;})
      `uvm_do_on(gpio_seq, p_sequencer.gpio0_seqr)
      `uvm_do_on_with(rd_rx_reg, p_sequencer.ahb_seqr, {base_addr == 'h820000;})
    end

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : apb_gpio_simple_vseq

class apb_subsystem_vseq extends uvm_sequence;

  function new(string name="apb_subsystem_vseq",
      uvm_sequencer_base sequencer=null, 
      uvm_sequence parent_seq=null);
      super.new(name);
  endfunction : new

  // Register sequence with a sequencer 
  `uvm_object_utils(apb_subsystem_vseq)
  `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)    

  // APB and UART UVC sequences
  u2a_incr_payload apb_to_uart;
  apb_spi_incr_payload apb_to_spi;
  apb_gpio_simple_vseq apb_to_gpio;

  virtual task body();
    uvm_test_done.raise_objection(this);

    `uvm_info("vseq", $sformatf("Doing apb_subsystem_vseq"), UVM_LOW)
    fork
      `uvm_do(apb_to_uart)
      `uvm_do(apb_to_spi)
      `uvm_do(apb_to_gpio)
    join

    uvm_test_done.drop_objection(this);
  endtask : body

endclass : apb_subsystem_vseq

class apb_ss_cms_seq extends uvm_sequence;

   `uvm_object_utils(apb_ss_cms_seq)
   `uvm_declare_p_sequencer(apb_subsystem_virtual_sequencer)

   function new(string name = "apb_ss_cms_seq");
      super.new(name);
   endfunction
  
   virtual task body();
    uvm_test_done.raise_objection(this);

    `uvm_info("vseq", $sformatf("Starting AHB Compliance Management System (CMS)"), UVM_LOW)
//	   p_sequencer.ahb_seqr.start_ahb_cms();  TODO: yet to implement

    uvm_test_done.drop_objection(this);
   endtask
     
endclass : apb_ss_cms_seq
`endif
