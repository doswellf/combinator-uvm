//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
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

// Test demonstrates concurrent TLM1 communication between SC and SV in 
// both directions

#include "uvm_ml.h"
using namespace tlm;
using namespace uvm_ml;
using namespace uvm;

#include "packet.h"

int N = getenv("N") ? atoi(getenv("N")) : 5;


// Template class of producer
// Produces 5 packets (17-21) and sends them through its ML analysis ports
// Two ports demonstrate different ways to define the port

template <typename T>
class producer : public uvm_component
{
public:
    tlm_analysis_port<T> aport;
    sc_port<tlm_analysis_if<T>, 2, SC_ONE_OR_MORE_BOUND > aport1;
    int cnt;
    unsigned int phase_count;
    bool btest_passed;

    UVM_COMPONENT_UTILS(producer)

    producer(sc_module_name name) : uvm_component(name), aport("aport"), aport1("aport1"), phase_count(0), btest_passed(true) { }


    void run_phase(uvm_phase *phase) 
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }


    void build_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void before_end_of_elaboration()
    {
        phase_count++;
        std::cout << "SC : before_end_of_elaboration - " << name() << std::endl;
    }

    void connect_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void end_of_elaboration_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void start_of_simulation_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void extract_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void check_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void report_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void final_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

        if (phase_count != 14)
        {
            std::cout << "ERROR: phasing error in component " << name() << " -> count = " << phase_count << std::endl; 
            btest_passed = false;
        }

    }

    void phase_started(uvm_phase *phase)
    {
    //    std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_started for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void phase_ready_to_end(uvm_phase *phase)
    {
     //   std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_ready_to_end for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void phase_ended(uvm_phase *phase)
    {
      //  std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_ended for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void reset_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void configure_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void main_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void shutdown_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

    }
};

UVM_COMPONENT_REGISTER_T(producer, packet)

// Template class of subscriber
// Prints the packets received through its export

template <typename T>
class subscriber : public uvm_component, public tlm_analysis_if<T> 
{
public:
    sc_export<tlm_analysis_if<T> > aexport;
    unsigned int phase_count;
    bool btest_passed;

    UVM_COMPONENT_UTILS(subscriber)

    subscriber(sc_module_name name) : uvm_component(name), aexport("aexport"), phase_count(0), btest_passed(true)
    {
        aexport(*this);
    }

    void write(const T& t) 
    {
        cout << "[SC " << sc_time_stamp() << "] " << name() << " subscriber::write: " << t;
    }

    void build_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void before_end_of_elaboration()
    {
        phase_count++;
        std::cout << "SC : before_end_of_elaboration - " << name() << std::endl;
    }

    void connect_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void end_of_elaboration_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void start_of_simulation_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void extract_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void check_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void report_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

    }

    void final_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

        // extra phase because added SC phase before_end_of_elaboration
        if (phase_count != 14)
        {
            std::cout << "ERROR: phasing error in component " << name() << " -> count = " << phase_count << std::endl; 
            btest_passed = false;
        }
    }

    void phase_started(uvm_phase *phase)
    {
        //std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_started for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void phase_ready_to_end(uvm_phase *phase)
    {
        //std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_ready_to_end for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void phase_ended(uvm_phase *phase)
    {
        //std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_ended for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void run_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void reset_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void configure_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void main_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void shutdown_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

    }

};
UVM_COMPONENT_REGISTER_T(subscriber, packet)

class env : public uvm_component
{
public:
    producer<packet>   *prod;
    subscriber<packet> *sub;
    unsigned int phase_count;
    bool bphase_started;
    bool bphase_ended;
    bool bphase_ready_to_end;
    bool btest_passed;
    bool bsctop_passed;

    UVM_COMPONENT_UTILS(env)

    env(sc_module_name name) : uvm_component(name), phase_count(0), bphase_started(false), bphase_ended(false), bphase_ready_to_end(false), btest_passed(true), bsctop_passed(true) { }

    void build_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        prod = new producer<packet>("producer");
        sub  = new subscriber<packet>("subscriber");
    }

    void before_end_of_elaboration()
    {
        phase_count++;
        std::cout << "SC : before_end_of_elaboration - " << name() << std::endl;
    }

    void connect_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        prod->aport(sub->aexport);
        prod->aport1(sub->aexport);
    }

    void end_of_elaboration_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void start_of_simulation_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void extract_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void check_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
    }

    void report_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

    }

    void final_phase(uvm_phase *phase)
    {
        phase_count++;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;

    }

    void phase_started(uvm_phase *phase)
    {
        bphase_started = true;

        std::cout << std::endl;
        std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_started for " << phase->get_name() << " - " << name() <<  std::endl;
    }

    void phase_ready_to_end(uvm_phase *phase)
    {
        bphase_ready_to_end = true;
        std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_ready_to_end for " << phase->get_name() << " - " << name() <<  std::endl;
    }


    void phase_ended(uvm_phase *phase)
    {
        bphase_ended = true;

        std::cout << "SC[" << sc_core::sc_time_stamp() << "] : phase_ended for " << phase->get_name() << " - " << name() <<  std::endl;

        if (strcmp(phase->get_name().c_str(), "build") == 0)
        {
            uvm_ml_register(&(prod->aport)); 
            uvm_ml_register(&(prod->aport1)); 
        }
        else if (strcmp(phase->get_name().c_str(), "final") == 0)
        {
            if (phase_count != 14)
            {
                std::cout << "ERROR: phasing error in component " << name() << " -> count = " << phase_count << std::endl; 
                btest_passed = false;
            }

            if (!bphase_started)
            {
                std::cout << "ERROR: phasing error in component " << name() << " phase_started never got call = " << std::endl; 
                btest_passed = false;
            }

            if (!bphase_ended)
            {
                std::cout << "ERROR: phasing error in component " << name() << " phase_ended never got call = " << std::endl; 
                btest_passed = false;
            }
            if (!bphase_ready_to_end)
            {
                std::cout << "ERROR: phasing error in component " << name() << " phase_ready_to_end never got call = " << std::endl; 
                btest_passed = false;
            }

            if (btest_passed && bsctop_passed && prod->btest_passed && sub->btest_passed)
                std::cout << "** UVM TEST PASSED **" << std::endl;
            else
                std::cout << "** UVM TEST FAILED **" << std::endl;
        }
    }

    void run_phase(uvm_phase *phase)
    {
        sc_core::sc_time dur(100, SC_NS);
        phase_count++;

        std::cout << std::endl;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Raising objection in " << phase->get_name() << " for 100 NS" << std::endl;

        phase->barrier.raise_barrier();

        wait(dur);

        phase->barrier.drop_barrier();
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Dropping objection in " << phase->get_name() << std::endl;
    }

    void reset_phase(uvm_phase *phase)
    {
        sc_core::sc_time dur(10, SC_NS);
        phase_count++;

        std::cout << std::endl;
        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Raising objection in " << phase->get_name() << " for 10 NS" << std::endl;

        phase->barrier.raise_barrier();

        wait(dur);

        phase->barrier.drop_barrier();
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Dropping objection in " << phase->get_name() << std::endl;
    }

    void configure_phase(uvm_phase *phase)
    {
        sc_core::sc_time dur(10, SC_NS);
        phase_count++;

        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Raising objection in " << phase->get_name() << " for 10 NS" << std::endl;

        phase->barrier.raise_barrier();

        wait(dur);

        phase->barrier.drop_barrier();
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Dropping objection in " << phase->get_name() << std::endl;
    }

    void main_phase(uvm_phase *phase)
    {
        sc_core::sc_time dur(10, SC_NS);
        phase_count++;

        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Raising objection in " << phase->get_name() << " for 10 NS" << std::endl;

        phase->barrier.raise_barrier();

        wait(dur);

        phase->barrier.drop_barrier();
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Dropping objection in " << phase->get_name() << std::endl;
    }

    void shutdown_phase(uvm_phase *phase)
    {
        sc_core::sc_time dur(10, SC_NS);
        phase_count++;

        std::cout << "SC : " << phase->get_name() << " - " << name() << std::endl;
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Raising objection in " << phase->get_name() << " for 10 NS" << std::endl;

        phase->barrier.raise_barrier();

        wait(dur);

        phase->barrier.drop_barrier();
        std::cout << "-- SC [" << sc_core::sc_time_stamp() << "] : Dropping objection in " << phase->get_name() << std::endl;

    }

};
UVM_COMPONENT_REGISTER(env)

// Top module contains a producer and a subscriber
// Registers the ports of the producer as ML
// The ports are bound in the SV code to 2 instances of subscriber

/*
class sctop : public uvm_component
{
public:

    UVM_COMPONENT_UTILS(sctop)
    
    env *my_env;

    sctop(sc_module_name name) : uvm_component(name), my_env(NULL) 
    { 
        cout << "In sctop constructor" << endl;
    }
    
    void build_phase (uvm_phase *phase)
    {
        cout << "In sctop::build_phase" << endl;
        my_env = new env("my_env");
    }

};
UVM_COMPONENT_REGISTER(sctop)
*/

SC_MODULE(sctop) {
    env my_env;
    bool btest_passed;
    unsigned int phase_count;
 
    SC_CTOR(sctop) : my_env("my_env"), btest_passed(true), phase_count(0) {
        cout << "sctop constructor" << endl;
    }

    void before_end_of_elaboration()
    {
        phase_count++;
        std::cout << "SC : before_end_of_elaboration - " << name() << std::endl;
    }

    void end_of_elaboration()
    {
        phase_count++;
        std::cout << "SC : end_of_elaboration - sctop" << std::endl;
    }

    void start_of_simulation()
    {
        phase_count++;
        std::cout << "SC : start_of_simulation - sctop" << std::endl;

        if (phase_count != 3)
        {
            std::cout << "ERROR: phasing error in module " << name() << " -> count = " << phase_count << std::endl; 
            btest_passed = false;
        }

        my_env.bsctop_passed = btest_passed;
    }

    void end_of_simulation()
    {
        // TODO: only called if sc_stop is called
        //       What happens in ML?
        std::cout << "SC : end_of_simulation - sctop" << std::endl;
    }

};

#ifndef NC_SYSTEMC
int sc_main(int argc, char** argv) {
  return 0;
}
#endif

UVM_ML_MODULE_EXPORT(sctop)

