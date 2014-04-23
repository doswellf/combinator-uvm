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

#ifndef BP_TOP_DESCRIPTOR_H
#define BP_TOP_DESCRIPTOR_H

namespace Bp {

//-------------------------------
//
// CLASS: BpTopDescriptorClass
//
// Represents a top-level component (test or a top)
//
//-------------------------------

class BpTopDescriptorBaseClass 
{
public:

    BpTopDescriptorBaseClass
    (
        const string & frameworkIndicator, 
        const string & compIdentifier,
        const string & instanceName,
        bool           isTest): 

            m_frmw_indicator(frameworkIndicator), 
            m_identifier(compIdentifier),
            m_instance_name(instanceName),
            m_is_test(isTest)
    {
        // This constructor is used when parsing command line arguments when the frameworks are not known yet
    }

    ~BpTopDescriptorBaseClass() {}

    ///////////////////////////////////////////////////////////////
    // Public Properties
    ///////////////////////////////////////////////////////////////
    const string &        GetInstanceName() const { return m_instance_name; }
    //
    void                  SetInstanceName(string name) { m_instance_name = name; }
    //
    const string &        GetIdentifier() const { return m_identifier; }
    //
    const string &        GetFrameworkIndicator() const { return m_frmw_indicator; }
    //
    bool                  IsTest() const { return m_is_test; }
    ///////////////////////////////////////////////////////////////

    void SetFrameworkTopLevelComponent();

    ////
    class InstanceNameComparer: public BpStringComparer 
    {
    public:
        InstanceNameComparer(string s): BpStringComparer(s) { }
        ~InstanceNameComparer() {};
        bool operator ()(BpTopDescriptorBaseClass *arg) { return (arg->GetInstanceName() == X()); }
    };
    ////

private:
    string                m_frmw_indicator;
    string                m_identifier;
    bool                  m_is_test;

    string                m_instance_name;
};

class BpTopDescriptorClass: public BpTopDescriptorBaseClass 
{
public:
    BpTopDescriptorClass (const BpTopDescriptorBaseClass * topArgument, 
                                FrameworkProxyClass *      frmwProxy): 

        BpTopDescriptorBaseClass
        (
            topArgument->GetFrameworkIndicator(), 
            topArgument->GetIdentifier(), 
            topArgument->GetInstanceName(),
            topArgument->IsTest()
        ),
            m_frmw_proxy(frmwProxy)
    { m_top_level_id = -1; }

    BpTopDescriptorClass(FrameworkProxyClass * frmwProxy,
                         int                   topLevelId,
                         const string &        compIdentifier,
                         string                instanceName,
                         bool                  isTest): 
                            BpTopDescriptorBaseClass(frmwProxy->GetName(), 
                                                     compIdentifier, instanceName, isTest), 
                            m_top_level_id(topLevelId),
                            m_frmw_proxy(frmwProxy) { }

    ~BpTopDescriptorClass() { }
    //
    FrameworkProxyClass * GetFrmw() { return m_frmw_proxy; }
    //
    int                   GetTopLevelId() { return m_top_level_id; }

    ///////////////////////////////////////////////////////////////
    // Public Interface
    ///////////////////////////////////////////////////////////////
    //
    int Instantiate();
    //
    int TransmitPhase (const char *        phaseGroup,
                       const char *        phaseName,
                       uvm_ml_phase_action phaseAction);

    ///////////////////////////////////////////////////////////////

    class PrefixComparer: public BpStringComparer 
    {
    public:
        PrefixComparer(string s): BpStringComparer(s) { }
        ~PrefixComparer() {};
        bool operator ()(BpTopDescriptorClass *arg) { 
            return BpPrefixCompare(arg->GetInstanceName(), X());
	}    
    };
private:
    FrameworkProxyClass * m_frmw_proxy;
    int                   m_top_level_id;
};

} // end namespace
#endif
