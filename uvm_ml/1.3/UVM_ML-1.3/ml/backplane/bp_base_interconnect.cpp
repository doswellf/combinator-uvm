//----------------------------------------------------------------------
//   Copyright 2012 Cadence Design Systems, Inc.
//   Copyright 2012-2013 Advanced Micro Devices Inc.
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

#include <iostream>
#include <string.h>
#include <algorithm>
#include <functional>

#include "bp_utils.h"
#include "bp_interconnect.h"
#include "bp_top_descriptor.h"
#include "bp_framework_proxy.h"

using namespace std;

extern void bp_printf(int debug_msg, const char *string,...);

namespace Bp 
{

bp_serror_t  *                        BpInterconnect::m_serror = 0;

bp_api_struct                         BpInterconnect::m_c_api_tray;

vector< FrameworkProxyClass * >       *BpInterconnect::m_framework_registry_p = 0;

vector< BpConnectionClass * >         BpInterconnect::m_port_registry;

vector< BpTopDescriptorClass * >      BpInterconnect::m_top_level_registry;

vector< BpChildProxyClass * >         BpInterconnect::m_child_proxy_registry;

map<string, vector< FrameworkProxyClass * > * > *BpInterconnect::m_frameworks_by_ind_p = 0;

BpTopDescriptorClass *                BpInterconnect::m_test_component = NULL;

int                                   BpInterconnect::m_trace_mode = 0;

bool                                  BpInterconnect::m_preInitial_cb_registered = false;

bool                                  BpInterconnect::m_elaboration_passed = false;

int                                   BpInterconnect::m_current_phase = 0;

string                                BpInterconnect::m_test_instance_name = "uvm_test_top"; // Default

map <string, uvm_ml_type_id_t>        BpInterconnect::m_unregistered_types;

map <uvm_ml_type_id_t, string>        BpInterconnect::m_unregistered_type_names;

vector <BpTypeMapEntryClass *>        BpInterconnect::m_registered_types;

vector< BpTopDescriptorBaseClass *>   BpInterconnect::m_top_arguments;

uvm_ml_time                           BpInterconnect::m_simulation_time = { TIME_UNIT_UNDEFINED, 0.0 };

frmw_srv_provider_struct              BpInterconnect::m_srv_providers;

FrameworkProxyClass *                 BpInterconnect::m_common_frmw;

vector< FrameworkProxyClass * >& BpInterconnect::GetFrameworkRegistry()
{
    if (m_framework_registry_p == 0) 
    {
        m_framework_registry_p = new vector< FrameworkProxyClass * >;
    }
    return *m_framework_registry_p;
}
map<string, vector< FrameworkProxyClass * > * >& BpInterconnect::GetFrameworksByInd()
{
    if (m_frameworks_by_ind_p == 0) 
    {
        m_frameworks_by_ind_p = new map<string, vector< FrameworkProxyClass * > * >;
    }
    return *m_frameworks_by_ind_p;
}


///////////////////////////////////////////////////////////////////////
// Implementation variables - we localize them in the .cpp file
// to separate between interface and implementation

BpInterconnect::BpInterconnect() 
{
}

BpInterconnect::~BpInterconnect() 
{
}

void BpInterconnect::ProcessTopsAndTests(vector<string> & tops, vector<string> & tests) 
{
     if (m_elaboration_passed ) 
     {
         // TODO : issue a warning here
	 bp_printf(BP_ERROR, "ProcessTopsAndTests called after elaboration");
         return;
     }

     if (tests.size() > 1) 
     {
         SERROR(MLUVM03, string("Multiple -uvmtest arguments")); // Only one test argument is legal
         throw 0;
     } 
     else if (tests.size() == 1)
     {
         identifyTestComponent(tests[0]);
     }

     if (tops.size() > 0)
         std::for_each(tops.begin(), tops.end(), identifyTopComponent);

}

bp_api_struct * BpInterconnect::Bootstrap(bp_preInitial_t * preInitial,
                                          vector<string>  & tops,
                                          vector<string>  & tests,
                                          bp_serror_t *     errorF)
{
    m_serror = errorF;

    fillCApiTray();

    // Do not process if empty
    if (tops.size() > 0 || tests.size() > 0) {
        try 
        {
            ProcessTopsAndTests(tops, tests);
        }
        catch (int ) 
        {
            // TODO: Add a message arguments parsing failed
	    bp_printf(BP_ERROR, "Bootstrap argument parsing failed");
            return (bp_api_struct * ) 0;
        }
    }

    if (preInitial) 
    {
        (*preInitial)(Elaborate, 0);
        m_preInitial_cb_registered = true;
    }

    return &m_c_api_tray; // return function tray

}   // Bootstrap

///
void BpInterconnect::identifyTestComponent(string & arg)
{
    string frameworkIdentifier;
    string compIdentifier;
    string instanceName;

    //assert (m_top_arguments.size() == 0); // Internal Error if it's not empty
    if (m_top_arguments.size() != 0) {
      bp_printf(BP_ERROR, "cannot define %s as the test componentbecause the test component is already defined", arg.c_str());
      throw 0;
    }

    ParseArgument(arg, frameworkIdentifier, compIdentifier, instanceName);

    if (compIdentifier.empty()) 
    {
        SERROR(MLUVM16, string ("Empty test component name in the -uvmtest command line argument"));
        throw 0;
    }
    if (frameworkIdentifier.empty()) 
    {
        SERROR(MLUVM16, string ("Empty language identifier in the -uvmtest command line argument"));
        throw 0;
    }
    if (instanceName.empty() == false && instanceName != m_test_instance_name)
    {
      cout << string("Backplane ERROR: uvmtest argument instance name identifier '") << instanceName << "' is not allowed.\n                 The only supported test instance name is uvm_test_top" << endl;
      bp_printf(BP_ERROR, "uvmtest argument instance name identifier '%s' is not allowed. The only supported test instance name is uvm_test_top", instanceName.c_str());
        throw 0;
    }  
    m_top_arguments.push_back(new BpTopDescriptorBaseClass(frameworkIdentifier, compIdentifier, m_test_instance_name, true));
}

///
void BpInterconnect::identifyTopComponent(string & arg)
{
    string frameworkIdentifier;
    string compIdentifier;
    string instanceName;


    ParseArgument(arg, frameworkIdentifier, compIdentifier, instanceName);

    if (compIdentifier.empty())
        SERROR(MLUVM16, "Empty top component name in the -uvmtop command line argument");

    if (frameworkIdentifier.empty())
        SERROR(MLUVM16, "Empty language identifier in the -uvmtop command line argument");

    if (instanceName == "")
        instanceName = compIdentifier;

    // Search for already existing name in list of -tops 
    if (std::find_if(m_top_arguments.begin(), m_top_arguments.end(), 
                     BpTopDescriptorBaseClass::InstanceNameComparer(instanceName)) != m_top_arguments.end())
        SERROR(MLUVM02, string("Multiple -uvmtop arguments with the same name: '") + instanceName + string("'"));

    m_top_arguments.push_back(new BpTopDescriptorBaseClass(frameworkIdentifier, compIdentifier, instanceName, instanceName == m_test_instance_name));
}

void BpInterconnect::ParseArgument(const string & arg, string & frameworkIndicator, string & compIdentifier, string &instanceName)
{
    size_t indicatorDelim = arg.find_first_of(":");

    //assert (indicatorDelim != string::npos) ; // TODO: add proper error message no framework indicator
    if (indicatorDelim == string::npos) {
      bp_printf(BP_ERROR, "colon delimiter missing in %s", arg.c_str());
      throw 0;
    }

    frameworkIndicator = arg.substr(0, indicatorDelim);
    std::transform(frameworkIndicator.begin(),frameworkIndicator.end(),frameworkIndicator.begin(),::tolower);
    size_t instanceNameDelim = arg.find_first_of(":", indicatorDelim + 1);
    if (instanceNameDelim == string::npos) {
        compIdentifier = arg.substr(indicatorDelim + 1); // Till the end of the string
        instanceName = "";
    }
    else {
      compIdentifier = arg.substr(indicatorDelim + 1, instanceNameDelim - indicatorDelim - 1);
      instanceName = arg.substr(instanceNameDelim + 1); 
    }
}

void BpInterconnect::ParseTypeName(const string & arg, string & frameworkIndicator, string & typeName)
{
    size_t indicatorDelim = arg.find_first_of(":");

    if (indicatorDelim == string::npos) {
      bp_printf(BP_ERROR, "colon delimiter missing in %s", arg.c_str());
    }
    assert (indicatorDelim != string::npos) ; // TODO: add proper error message no framework indicator

    frameworkIndicator = arg.substr(0, indicatorDelim);
    std::transform(frameworkIndicator.begin(),frameworkIndicator.end(),frameworkIndicator.begin(),::tolower);
    typeName = arg.substr(indicatorDelim + 1); // Till the end of the string
}

int BpInterconnect::RegisterFramework( string &               frameworkName,
                                       vector<string> &       frameworkIndicators,
                                       bp_frmw_c_api_struct * requiredApi)
{
    if (requiredApi == NULL) 
    {
        // TODO:    SERROR(MLUVM17, string("Framework ") + FrameworkIndicator + " API tray pointer is null");
        cout << string("Framework ") + frameworkName + "Required API tray pointer is null" << endl;
        return (-1);
    }
    FrameworkProxyClass * frmw = GetFrameworkProxyByName(frameworkName);

    if (frmw != NULL)
        return frmw->GetFrameworkId();
    else
        return addFramework(frameworkName, frameworkIndicators, requiredApi);
}  

int BpInterconnect::addFramework( string &               frameworkName, 
                                  vector<string> &       frameworkIndicators,
                                  bp_frmw_c_api_struct * requiredApi)
{
    int id = GetFrameworkRegistry().size();
    FrameworkProxyClass * newFrmw = new FrameworkProxyClass(id, frameworkName, frameworkIndicators, requiredApi);
    GetFrameworkRegistry().push_back(newFrmw);

    return id;
}

FrameworkProxyClass * BpInterconnect::GetFramework(int frameworkId)
{
    return GetFrameworkRegistry()[frameworkId];
}

void BpInterconnect::AddFrmwIndicator(string indicator, FrameworkProxyClass * frmw)
{
    // The argument indicator is passed by copy intentionally
    std::transform(indicator.begin(),indicator.end(),indicator.begin(),::tolower);

    map<string, vector< FrameworkProxyClass * > *>::iterator it = GetFrameworksByInd().find(indicator);
 
    vector< FrameworkProxyClass * > * frmws;

    if (it == GetFrameworksByInd().end()) {
 
        frmws = new vector< FrameworkProxyClass * >;
        GetFrameworksByInd()[indicator] = frmws;
    }
    else
        frmws = GetFrameworksByInd()[indicator];

    frmws->push_back(frmw);
}

int BpInterconnect::AddRootNode (int            frameworkId, 
                                 int            topComponentId,
                                 const string & compIdentifier,
                                 const string & instanceName)
{
    FrameworkProxyClass * frmw = GetFrameworkRegistry()[frameworkId];

    vector< BpTopDescriptorClass * >::iterator it = 
        std::find_if(m_top_level_registry.begin(), m_top_level_registry.end(), BpTopDescriptorClass::InstanceNameComparer(instanceName));

    if (it != m_top_level_registry.end()) 
    {
        if ((*it)->GetFrmw() == frmw)
        {
            return 0; // already registered
        }
        else 
        {
	    SERROR3(MLUVM01, "UVM-ML Bp Error: Id = %d, multiple top levels with the same name in different languages: top name is '%s', first language is '%s', second language is '%s'\n", instanceName, frmw->GetName().c_str(), (*it)->GetFrmw()->GetName().c_str());
            return (-1);
        }
    }

    BpTopDescriptorClass * comp = new BpTopDescriptorClass(frmw, topComponentId, compIdentifier, instanceName, instanceName == m_test_instance_name);
    
    frmw->PushTopLevel(comp);
    AddTopLevel(comp);
    
    return 1;
}

void BpInterconnect::AddTopLevel (BpTopDescriptorClass * topComponent) 
{ 
    m_top_level_registry.push_back(topComponent); 
    if (topComponent->IsTest()) 
    {
        if (m_test_component != NULL) {
	  bp_printf(BP_ERROR, "Test component was not registered as test");
        }
        assert (m_test_component == NULL); // TODO: make it a proper error
        m_test_component = topComponent;
    }
};

FrameworkProxyClass * BpInterconnect::GetFrameworkProxyByName(const string & frameworkName)
{
    vector< FrameworkProxyClass * >::iterator it = std::find_if(GetFrameworkRegistry().begin(), 
                                                                GetFrameworkRegistry().end(), 
                                                                FrameworkProxyClass::FrameworkNameComparer(frameworkName));
    return ((it == GetFrameworkRegistry().end()) ? NULL : *it);
}

FrameworkProxyClass * BpInterconnect::GetFrameworkProxyByInd(string frameworkIndicator)
{
    
    // The argument indicator is passed by copy intentionally
    std::transform(frameworkIndicator.begin(),frameworkIndicator.end(),frameworkIndicator.begin(),::tolower);

    map<string, vector< FrameworkProxyClass * > *>::iterator it = GetFrameworksByInd().find(frameworkIndicator);
    if (it == GetFrameworksByInd().end()) // legitimate (for example, for type match settings
        return NULL;
        
    vector< FrameworkProxyClass * > * frmws = GetFrameworksByInd()[frameworkIndicator];
    if (frmws == NULL) {
      bp_printf(BP_ERROR, "Cannot locate framework because the list is empty");
      return NULL;
    }
    //assert (frmws != NULL);

    if (frmws->size() > 1) {
        cout << string("Backplane ERROR: There are more than one registered framework that matches the indicator '") << frameworkIndicator << "': " << endl; // TODO: Make it a proper error message
        cout << string("              ");
        for (int j = 0; j < frmws->size(); j++) {
	    cout << (*frmws)[j]->GetName();
           if (j < (frmws->size() - 1))
               cout << string(", ");
	   else
	       cout << endl;
	}
        exit(-1);
    } else
        return (*frmws)[0];
}

void BpInterconnect::SERROR(int msgId, string msg)
{
    if (m_serror)
    {
        (*m_serror)(msgId, msg.c_str());
    }
    else 
    {
        printf("UVM-ML Bp Error: Id = %d, msg = %s\n", msgId, msg.c_str());
        exit(-1);
    }
}

void BpInterconnect::SERROR2(int msgId, const char* fmt, string msg, string msg1)
{
    if (m_serror)
    {
      (*m_serror)(msgId, msg.c_str(), msg1.c_str());
    }
    else 
    {
      //printf("UVM-ML Bp Error: Id = %d, msg = %s\n", msgId, msg.c_str());
      printf(fmt, msgId, msg.c_str(), msg1.c_str());
      exit(-1);
    }
}
void BpInterconnect::SERROR3(int msgId, const char* fmt, string msg, string msg1, string msg2)
{
    if (m_serror)
    {
      (*m_serror)(msgId, msg.c_str(), msg1.c_str(), msg2.c_str());
    }
    else 
    {
       printf(fmt, msgId, msg.c_str(), msg1.c_str(), msg2.c_str());
       exit(-1);
    }
}

void BpInterconnect::SetTraceMode(int mode)
{
    m_trace_mode = mode;
    std::for_each(GetFrameworkRegistry().begin(), GetFrameworkRegistry().end(), std::bind2nd(std::mem_fun(&FrameworkProxyClass::SetTraceMode), m_trace_mode));
}

//==============================================================================
// ---- PHASING
//==============================================================================

//------------------------------------------------------------------------------
/*! Called at the end of Elaborate() to start phasing the frameworks.
 * 
 */
void BpInterconnect::StartPhasing()
{
    if (m_srv_providers.phase_srv_provider)
    {
        bp_printf(BP_DEBUG, "BpInterconnect::StartPhasing Phase Master =  %s\n", m_srv_providers.phase_srv_provider->GetName().c_str());
        m_srv_providers.phase_srv_provider->StartPhasing();
    }
    else
    {
        bp_printf(BP_ERROR, "BpInterconnect::StartPhasing() - No phase service registered.");
    }
}

//------------------------------------------------------------------------------
/*! Called by the phase master to notify a non-runtime phase (phase that 
 *  doesn't consume time).
 * 
 *  Backplane will notify each registered framework of the phase and then
 *  notify each registered top of the phase.
 *
 *  Some frameworks have phases that applied to the entire framework and 
 *  are not hierarchical, therefore the backplane splits the notify_phase()
 *  called by the master phase controller into two calls.  One to the 
 *  framework (notify_phase), so it can executed any framework specific
 *  phasing and then to the top components (transmit_phase) to do 
 *  hierachical phasing.
 * 
 */
int BpInterconnect::NotifyPhase
(
    unsigned int        frameworkId,
    const char *        phaseGroup,
    const char *        phaseName,
    uvm_ml_phase_action phaseAction
)
{
    static bool bCheckConnection = false;
    int         result           = 1;

    // Check the connection before the start of simulation phase
    // -> at the end of end_of_elaboration
    if (strcmp(phaseName, "start_of_simulation") == 0)
    {
        //TODO: what to do if there was a connection error??
        bCheckConnection = true;
        checkAllConnections();
    }

    if (phaseAction == UVM_ML_PHASE_STARTED || phaseAction == UVM_ML_PHASE_EXECUTING) {
        for (int i = 0; i < GetFrameworkRegistry().size(); i++) {
            FrameworkProxyClass * frmw = GetFrameworkRegistry()[i];
            result = frmw->NotifyPhase(phaseGroup, phaseName, phaseAction);
            if (result == 0) // failed
	    {
                bp_printf(BP_ERROR, "BpInterconnect::NotifyPhase(): framework = %s[%0d] returned with error.", frmw->GetName().c_str(), frmw->GetFrameworkId());
                return result;
            }
        }
    }

    for (int i = 0; i < m_top_level_registry.size(); i++)
    {
        BpTopDescriptorClass * it = m_top_level_registry[i];
        result = it->TransmitPhase(phaseGroup, phaseName, phaseAction);
        if (result == 0) // failed
        {
            bp_printf(BP_ERROR, "BpInterconnect::NotifyPhase(): top = %s[%s] returned with error.", it->GetInstanceName().c_str(), it->GetFrameworkIndicator().c_str());
            return result;
	}
    }

    if (phaseAction == UVM_ML_PHASE_READY_TO_END || phaseAction == UVM_ML_PHASE_ENDED) {
        for (int i = 0; i < GetFrameworkRegistry().size(); i++) {
            FrameworkProxyClass * frmw = GetFrameworkRegistry()[i];
            result = frmw->NotifyPhase(phaseGroup, phaseName, phaseAction);
            if (result == 0) // failed
	    {
                bp_printf(BP_ERROR, "BpInterconnect::NotifyPhase(): framework = %s[%0d] returned with error.", frmw->GetName().c_str(), frmw->GetFrameworkId());
                return result;
	    }
        }
    }
    return result;
}

//------------------------------------------------------------------------------
/*! Called by hierachical parent to notify child of a phase.
 * 
 *  In a unified hierarchy, a child proxy is created for a component that
 *  is in another framework. This child proxy is connected through the
 *  backplane to a parent proxy.  All non-time consuming phase notification
 *  the child proxy receieves is passed to the parent proxy through
 *  the bp_transmit_phase() called.  Runtime (time consuming) phases are
 *  non-hierarchical, and are phased by the framework when it recevies
 *  notification.
 */
int BpInterconnect::TransmitPhase
(
    unsigned int        frameworkId,
    const string &      target_frmw_ind,
    int                 targetId,
    const char *        phaseGroup,
    const char *        phaseName,
    uvm_ml_phase_action phaseAction
)
{
    int          result = 0;
    FrameworkProxyClass *frmw = GetFrameworkProxyByInd(target_frmw_ind);
    //assert (frmw != NULL);
    if(frmw == NULL) {
      bp_printf(BP_ERROR, "No framework with name '%s' has been registered", target_frmw_ind.c_str());
      return 0;
    };

    result = frmw->TransmitPhase(targetId, phaseGroup, phaseName, phaseAction);
    if (result == 0) 
        bp_printf(BP_ERROR, "BpInterconnect::TransmitPhase(): %s[%0d] framework returned with error for target_id = %0d.", frmw->GetName().c_str(), frmw->GetFrameworkId(), targetId);

    return result;
}

//------------------------------------------------------------------------------
/*! Called by the phase master to notify a runtime phase (phase that consumes time).
 * 
 *  Runtime phases are not hierachical so they are only passed on to each 
 *  framework and not the tops.
 */
int BpInterconnect::NotifyRuntimePhase
(
    unsigned int        frameworkId,
    const char *        phaseGroup,
    const char *        phaseName,
    uvm_ml_phase_action phaseAction,
    uvm_ml_time_unit    timeUnit,
    double              timeValue,
    unsigned int *      participate
)
{
    unsigned int participateCount = 0;
    unsigned int participateTotal = 0;
    int          result = 0;

    for (int i = 0; i < GetFrameworkRegistry().size(); i++)
    {
        participateCount = 0;
        result = GetFrameworkRegistry()[i]->NotifyRuntimePhase(phaseGroup, phaseName, phaseAction, timeUnit, timeValue, &participateCount);
        participateTotal += participateCount;
    }

    (*participate) = participateTotal;

    return result;
}

//------------------------------------------------------------------------------
/*! Register a common services framework with the backplane.
 *  
 *  Common service framework is a special framework.  It is not in the framework
 *  registry.  This framework only provides serivces and does not participate
 *  in phasing/synchronization/transaction ...
 * 
 */
void BpInterconnect::RegisterCommonSrvFrmw(FrameworkProxyClass * frmw)
{
    m_common_frmw = frmw;
}  

//------------------------------------------------------------------------------
/*! Register which framework will provide which service.
 */
void BpInterconnect::RegisterSrvProviders(unsigned int frameworkId, bp_srv_provider_struct *srv_providers)
{
    FrameworkProxyClass *frmw = NULL;

    // phase service
    if (strcmp(srv_providers->phase_srv_provider, "") > 0)
    {
        frmw = findServiceFrmw(srv_providers->phase_srv_provider);
        if (frmw)
        {
            bp_printf(BP_DEBUG, "BpInterconnect Registering Phase Master =  %s\n", frmw->GetName().c_str());
            m_srv_providers.phase_srv_provider = frmw;
        }
        else
        {
            bp_printf(BP_WARNING, "BpInterconnect::RegisterSrvProviders() Phase service framework not found : %s", srv_providers->phase_srv_provider);
        }
    }

}

//------------------------------------------------------------------------------
/*! Helper function that finds pointer to the service provider framework.
 * 
 *  Common service framework is a special framework.  It is not in the framework
 *  registry.  This framework only provides serivces and does not participate
 *  in phasing/synchronization/transaction ...
 *  
 */
FrameworkProxyClass * BpInterconnect::findServiceFrmw(const char * name)
{
    FrameworkProxyClass *frmw = NULL;

    if (strcmp(name, m_common_frmw->GetName().c_str()) == 0)
        frmw = m_common_frmw;
    else
        frmw = GetFrameworkProxyByName(name);

    return frmw;
}

//------------------------------------------------------------------------------
/*! Called by the framework and passed to the phase master to notify that
 *  the framework is ready to exit the phase.
 */
void BpInterconnect::PhaseSrvNotifyPhaseDone
(
    unsigned int      frameworkId,
    const char *      phaseGroup,
    const char *      phaseName,
    uvm_ml_time_unit  timeUnit,
    double            timeValue
)
{
    if (m_srv_providers.phase_srv_provider)
    {
        m_srv_providers.phase_srv_provider->PhaseSrvNotifyPhaseDone(frameworkId, phaseGroup, phaseName, timeUnit, timeValue);
    }
    else
    {
        bp_printf(BP_ERROR, "BpInterconnect::PhaseSrvNotifyPhaseDone() - No phase service registered.");
    }
}

void BpInterconnect::instantiateTop(BpTopDescriptorClass * top)
{
    if (top->Instantiate() < 0)
        throw 0; // The framework adapter is responsible to issue the error message. This function allows to stop further phasing
}

int BpInterconnect::Elaborate(void *cbInfo)
{
    if (m_elaboration_passed) {
        bp_printf(BP_WARNING, "BpInterconnect::Elaborate() - Elaborate called after elaboration time has passed.");
        return 0;
    }

    if (m_top_arguments.size() == 0)
        return 0; // If there were no root nodes specified on the command line
                  // let them to be passed procedurally via bp_run_test()

    m_elaboration_passed = true;

    if (getenv("UVM_ML_DEBUG_MODE"))
        SetTraceMode(1);

    setComponentFrameworks(); // At this point all framework proxies and top components shall be registered 

    try 
    {
        std::for_each(GetFrameworkRegistry().begin(), GetFrameworkRegistry().end(), std::mem_fun(&FrameworkProxyClass::Startup));
    }
    catch (int)
    {
	bp_printf(BP_ERROR, "Elaborate failed");
        return 0;
    }

    // std::for_each(m_top_level_registry.begin(), m_top_level_registry.end(), std::mem_fun(&BpTopDescriptorClass::Instantiate));

    try 
    {
        std::for_each(m_top_level_registry.begin(), m_top_level_registry.end(), instantiateTop);
    }
    catch (int)
    {
        return 0;
    }
    // -- Phasing
    StartPhasing();

    return 1;
}

void BpInterconnect::setComponentFrameworks()
{
    std::for_each(m_top_arguments.begin(), m_top_arguments.end(), (std::mem_fun(&BpTopDescriptorBaseClass::SetFrameworkTopLevelComponent)));
}

BpChildProxyClass * BpInterconnect::findChildProxyforPath(const string & path)
{
    BpChildProxyClass * result = NULL;

    BpChildProxyClass * c_proxy = NULL;
    size_t longest_match_length = 0;

    for (int j = 0; j < m_child_proxy_registry.size(); j++) {
        // Looking for the longest match among the child proxies
        c_proxy = m_child_proxy_registry[j];
   
        const string & proxy_full_name = c_proxy->GetName();
        int prefix_len = proxy_full_name.length();

        if ((prefix_len > longest_match_length) && 
            BpPrefixCompare(proxy_full_name, path)) {
            // longest match found
	    longest_match_length = prefix_len;
            result = c_proxy;        
	}
    }
    return result;
}

FrameworkProxyClass * BpInterconnect::findFrameworkForPath(const string &path)
{
    // Looking for the matching prefix first among the child proxies
    // and if not found - among the root nodes

    BpChildProxyClass * c_proxy = findChildProxyforPath(path);

    if (c_proxy != NULL)
    {
        return GetFramework(c_proxy->GetTargetFrameworkId());
    }

    if (BpPrefixCompare(m_test_instance_name, path))
    {
        if(m_test_component == NULL) {
	  bp_printf(BP_ERROR, "The instance name 'uvm_test_top' cannot be used in absence of a test component");
	  return NULL;
	};
        //assert (m_test_component != NULL); // TODO: add an error message
                                           // saying that the instance name 
                                           // "uvm_test_top" cannot be used 
                                           // in absence of a test component
        return m_test_component->GetFrmw();
    }

    vector< BpTopDescriptorClass * >::iterator it = 
        std::find_if(m_top_level_registry.begin(),m_top_level_registry.end(), 
                     BpTopDescriptorClass::PrefixComparer(path));

    if (it != m_top_level_registry.end())
    {
        return ((*it)->GetFrmw());
    }
    else {
        SERROR(MLUVM06, 
               string("Could not find a UVM-ML framework for connection name '") + path + "' specified in UVM-ML connection function.");
        return ((FrameworkProxyClass *)0);
    }
}

BpConnectionClass *  BpInterconnect::AddConnection(string path)
{
    FrameworkProxyClass * frmw = findFrameworkForPath(path);
    if (frmw == NULL)
        return NULL;

    int bind_key = frmw->GetConnectionBindKey(path);
    if (bind_key == (-1)) 
    {
        SERROR(MLUVM09, string(path));
        return NULL;
    }

    string intf_name = frmw->GetConnectionIntfName(bind_key);

    BpConnectorKind kind = frmw->GetConnectionKind(bind_key);

    BpConnectionClass * result = new BpConnectionClass(frmw, bind_key, path, intf_name, kind);

    m_port_registry.push_back(result);

    frmw->AddConnection(result, bind_key);

    return result;
}

BpConnectionClass * BpInterconnect::FindConnectionByName(const string & path)
{
    vector< BpConnectionClass * >::iterator it = std::find_if(m_port_registry.begin(), m_port_registry.end(), 
            BpConnectionClass::PathComparer(path));
    return (it == m_port_registry.end() ? NULL : *it);
}

bool BpInterconnect::checkAllConnections()
{
    bool result = true;
    vector< BpConnectionClass * >::iterator it;
    for (it = m_port_registry.begin(); it != m_port_registry.end(); it++)
    {
        result = result && ((*it)->CheckCompatibility());
    }

    return result;
}

uvm_ml_type_id_t BpInterconnect::GetTypeIdByTypeName(int            frameworkId,
                                                     const string & typeName)
{
    return (uvm_ml_type_id_t) GetFramework(frameworkId)->GetTypeId(typeName);
}

string BpInterconnect::GetTypeNameByTypeId(int              frameworkId,
                                           uvm_ml_type_id_t typeId,
                                           bool             getBaseName)
{
    return GetFramework(frameworkId)->GetTypeName(typeId, getBaseName);
}

// /////////////////////////////////////////////////
// registerNewTypeMatch() is a private member function
// It is invoked from RegisterTypeMatch() if both types are
// new to the bp
// /////////////////////////////////////////////////

void BpInterconnect::registerNewTypeMatch(FrameworkProxyClass * t1Frmw, 
                                          const string &        t1Name, 
                                          FrameworkProxyClass * t2Frmw, 
                                          const string &        t2Name)
{
    BpTypeMapEntryClass * entry = new BpTypeMapEntryClass(GetNextTypeId());

    entry->AddFrmwEntry(new FrameworkTypeEntryClass(t1Frmw, t1Name));
    entry->AddFrmwEntry(new FrameworkTypeEntryClass(t2Frmw, t2Name));

    t1Frmw->AddRegisteredTypeEntry(t1Name, entry);
    t2Frmw->AddRegisteredTypeEntry(t2Name, entry);
}

bool BpInterconnect::RegisterTypeMatch(BpLangTypeName & type1,
                                       BpLangTypeName & type2)
{
    FrameworkProxyClass * t1_frmw = GetFrameworkProxyByInd(type1.GetLangIndicator());
    if (t1_frmw == NULL)
        return false; // It is legal to call RegisterTypeMatch for a framework which is currently not active

    FrameworkProxyClass * t2_frmw = GetFrameworkProxyByInd(type2.GetLangIndicator());
    if (t2_frmw == NULL)
        return false; // It is legal to call RegisterTypeMatch for a framework which is currently not active

    if(t1_frmw == t2_frmw) {
      bp_printf(BP_ERROR, "Cannot associate two type names for the same framework");
    };
    assert (t1_frmw != t2_frmw); // TODO: Otherwise issue a proper error message
    // "Cannot associate two type names for the same framework"

    // Look if those type names already appeared (either in a previous explicit type match (registered)
    // or at runtime as an actual transaction type
    uvm_ml_type_id_t t1_id = t1_frmw->FindTypeId(type1.GetTypeName());
    uvm_ml_type_id_t t2_id = t2_frmw->FindTypeId(type2.GetTypeName());

    if ((t1_id == (-1)) && (t2_id == (-1)))
    {
      registerNewTypeMatch(t1_frmw, type1.GetTypeName(), t2_frmw, type2.GetTypeName());
    }
    else if (t2_id == (-1)) 
    {
        BpTypeMapEntryClass * t1_map_entry = t1_frmw->FindRegisteredTypeEntry(t1_id);
	if(t1_map_entry == NULL) {
	  bp_printf(BP_ERROR, "RegisterTypeMatch() was called late, after an object of unregistered Type1 appeared in a transaction");
	};
        assert (t1_map_entry != NULL); // TODO: Otherwise issue a proper error 
        // that RegisterTypeMatch() was called late - 
        // after an object of unregistered Type1 appeared in a transaction
        t1_map_entry->AddFrmwTypeEntry(t2_frmw, type2.GetTypeName());
        t2_frmw->AddRegisteredTypeEntry(type2.GetTypeName(), t1_map_entry);
    } 
    else if (t1_id == (-1)) 
    {
        BpTypeMapEntryClass * t2_map_entry = t2_frmw->FindRegisteredTypeEntry(t2_id);
	if(t2_map_entry == NULL) {
	  bp_printf(BP_ERROR, "RegisterTypeMatch() was called late, after an object of unregistered Type2 appeared in a transaction");
	};
        assert (t2_map_entry != NULL); // TODO: Otherwise issue a proper error 
        // that RegisterTypeMatch() was called late - 
        // after an object of unregistered Type2 appeared in a transaction
        t2_map_entry->AddFrmwTypeEntry(t1_frmw, type1.GetTypeName());
        t1_frmw->AddRegisteredTypeEntry(type1.GetTypeName(), t2_map_entry);
    } 
    else if (t1_id != t2_id) 
    {
        BpTypeMapEntryClass * t1_map_entry = t1_frmw->FindRegisteredTypeEntry(t1_id);
	if(t1_map_entry == NULL) {
	  bp_printf(BP_ERROR, "RegisterTypeMatch() was called late, after an object of unregistered Type1 appeared in a transaction");
	};
        assert (t1_map_entry != NULL); // TODO: Otherwise issue a proper error 
        // that RegisterTypeMatch() was called late - 
        // after an object of unregistered Type1 appeared in a transaction
        BpTypeMapEntryClass * t2_map_entry = t2_frmw->FindRegisteredTypeEntry(t2_id);
	if(t2_map_entry == NULL) {
	  bp_printf(BP_ERROR, "RegisterTypeMatch() was called late, after an object of unregistered Type2 appeared in a transaction");
	};
        assert (t2_map_entry != NULL); // TODO: Otherwise issue a proper error 
        // that RegisterTypeMatch() was called late - 
        // after an object of unregistered Type2 appeared in a transaction
        mergeTypeEntries(t1_map_entry, t2_map_entry);
    } // else this pair of types was already registered before and nothing shall be done
    return true;
}

void BpInterconnect::mergeTypeEntries(BpTypeMapEntryClass * entry1, 
                                      BpTypeMapEntryClass * entry2)
{
    bp_printf(BP_ERROR, "mergeTypeEntries not supported");
    assert (false); // TODO
}

uvm_ml_type_id_t BpInterconnect::GetUnregisteredTypeId(const string & typeName)
{
    map<string, uvm_ml_type_id_t>::iterator it = m_unregistered_types.find(typeName);
    if (it != m_unregistered_types.end())
        return it->second;

    uvm_ml_type_id_t type_id = GetNextTypeId();
    m_unregistered_types[typeName] = type_id;
    m_unregistered_type_names[type_id] = typeName;
    return type_id;    
}

const string & BpInterconnect::FindUnregisteredTypeName(uvm_ml_type_id_t typeId)
{
    map<uvm_ml_type_id_t, string>::iterator it = m_unregistered_type_names.find(typeId);

    if(it == m_unregistered_type_names.end()) {
      bp_printf(BP_ERROR, "FindUnregisteredTypeName: type was not found");
    };
    assert (it != m_unregistered_type_names.end()); // TODO: Issue a proper internal error message
    // about a wrong TypeId
    return it->second;
}

void BpInterconnect::AddRegisteredTypeEntry(BpTypeMapEntryClass * entry)
{
    m_registered_types.push_back(entry);
}

uvm_ml_type_id_t BpInterconnect::GetNextTypeId()
{
    static uvm_ml_type_id_t next_id = 0; // TODO make it a class member - in order to enable reset
    return next_id++;
}

void BpInterconnect::Synchronize(int              framework_id,
                                 uvm_ml_time_unit timeUnit,
                                 double           timeValue)
{
    for (int j = 0; j < GetFrameworkRegistry().size(); j++)
        if (GetFrameworkRegistry()[j]->GetFrameworkId() != framework_id)
	  GetFrameworkRegistry()[j]->Synchronize(timeUnit, timeValue);
}

int BpInterconnect::GetConnectorSize(int framework_id, int connector_id)
{
    FrameworkProxyClass *frmw = GetFramework(framework_id);
    if(frmw == NULL) {
      bp_printf(BP_ERROR, "Framework was not found, ID is %d", framework_id);
      return -1;
    };
    //assert (frmw != NULL);
    BpConnectionClass * con = frmw->GetConnection(connector_id);
    if (con != NULL) 
    {
        return con->GetSize();
    }
    else 
    {
        return 0; // Legal situation if an export (or "imp") remained unbound
    }
}

void BpInterconnect::NotifyConfig(int              framework_id,
                                  const char *     cntxt,
                                  const char *     instance_name,
                                  const char *     field_name,
                                  unsigned int     stream_size,
                                  uvm_ml_stream_t  stream,
                                  uvm_ml_time_unit time_unit, 
                                  double           time_value)
{
    for (int i = 0; i < GetFrameworkRegistry().size(); i++)
    {
        FrameworkProxyClass * frmw = GetFrameworkRegistry()[i];
        if (frmw->GetFrameworkId() != framework_id)
            frmw->NotifyConfig(cntxt, instance_name, field_name, stream_size, stream, time_unit, time_value);
    }    
}

string BpInterconnect::GetVersion() 
{
    return UVM_ML_VERSION;
}

} // end namespace

