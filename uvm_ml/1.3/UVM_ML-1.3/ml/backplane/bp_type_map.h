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

// Backplane Type Map module header File
// bp_type_map.h

#ifndef BP_TYPE_MAP_H
#define BP_TYPE_MAP_H

#include <vector>
#include <string>
#include <map>
#include <assert.h>

#include "bp_common_c.h"

using namespace std;
//////////////

namespace Bp {

class BpTypeMapEntryClass;

class FrameworkProxyClass;

//-------------------------------------------------
//
// CLASS: FrameworkTypeEntryClass
//
// Represents one element (of the list of elements m_matching_types) 
// in the entry (of type BpTypeMapEntryClass) in the vector of 
// matching registered types (BpInterconnect::m_registered_types
// Contains a pair: framework proxy and type name
//
//-------------------------------------------------

class FrameworkTypeEntryClass 
{
public:
    FrameworkTypeEntryClass(FrameworkProxyClass * frmw, const string & name): 
        m_frmw(frmw), 
        m_name(name) 
    {}

    ~FrameworkTypeEntryClass() {};

    ///////////////////////////////////////////////////////////////
    // Public Interface Methods
    ///////////////////////////////////////////////////////////////
    //
    uvm_ml_type_id_t GetTypeId();
    //
    const string & GetTypeName() { return m_name; }
    //
    FrameworkProxyClass * GetFrameworkProxy() { return m_frmw; }
    //
    BpTypeMapEntryClass * GetRegisteredTypeEntry() { return m_bp_type_map_entry; }
    //
    void SetRegisteredTypeEntry(BpTypeMapEntryClass * Entry) { m_bp_type_map_entry = Entry; }
private:
    FrameworkProxyClass * m_frmw;
    string                m_name;
    BpTypeMapEntryClass * m_bp_type_map_entry;
};

//-------------------------------------------------
//
// CLASS: BpLangTypeName
//
// Represents an argument of explicit type mapping call
// Contains a pair: framework language indicator and type name
//
//-------------------------------------------------

struct BpLangTypeName 
{

    BpLangTypeName(const string & lang, const string & type)
    {
        m_framework_lang_indicator = lang;
        m_type_name = type;
    }

    const string & GetTypeName() { return m_type_name; }
    const string & GetLangIndicator() { return m_framework_lang_indicator; }

    string m_framework_lang_indicator;
    string m_type_name;
};

//-------------------------------------------------
//
// CLASS: BpTypeMapEntryClass
//
// Represents an entry in the in the vector of 
// matching registered types (BpInterconnect::m_registered_types
//
//-------------------------------------------------

class BpTypeMapEntryClass 
{
public:

    BpTypeMapEntryClass(int id): m_type_id(id) {}
    ~BpTypeMapEntryClass() {}
    // 
    uvm_ml_type_id_t          GetTypeId() { return m_type_id; }
    //
    void                      AddFrmwEntry(FrameworkTypeEntryClass * FrmwTypeEntry);
    //
    void                      AddFrmwTypeEntry(FrameworkProxyClass * frmw, const string & TypeName);
    //
    FrameworkTypeEntryClass * FindFrmwEntry(const FrameworkProxyClass * frmw);


//-------------------------------------------------
//
// CLASS: BpTypeMapEntryClass::FrameworkComparer
//
// A functor class that is used for finding a vector element matching
// the given framework proxy pointer
//
//-------------------------------------------------

    class FrameworkComparer 
    {
    public:
        FrameworkComparer(const FrameworkProxyClass * frmw) { x = frmw; }
        ~FrameworkComparer() {}
        const FrameworkProxyClass * X() { return x; }

        bool operator()(FrameworkTypeEntryClass * arg) { return arg->GetFrameworkProxy() == X(); }
    private:
        const FrameworkProxyClass * x;
    };

private:
    uvm_ml_type_id_t                  m_type_id;
    vector<FrameworkTypeEntryClass *> m_matching_types;
};

} // namespace Bp
#endif /* BP_TYPE_MAP_H */
