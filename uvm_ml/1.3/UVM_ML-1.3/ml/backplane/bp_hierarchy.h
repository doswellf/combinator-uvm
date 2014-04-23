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

#ifndef BP_HIERARCHY_H
#define BP_HIERARCHY_H

// Parent component proxy representation header File
// bp_hierarchy.h

#include <vector>
#include <map>
#include <strings.h>
#include "bp_utils.h"

using namespace std;

namespace Bp {

class BpChildProxyClass {

public:

    BpChildProxyClass(const string & instanceName,
                      const string & parentFullName,
                      int            targetFrameworkId);
    virtual ~BpChildProxyClass() {}

    const string & GetName() { return m_full_name; }
    int            GetTargetFrameworkId() { return m_target_framework_id; }

    class PrefixComparer: public BpStringComparer 
    {
    public:
        PrefixComparer(string s): BpStringComparer(s) { }
        ~PrefixComparer() {};
        bool operator ()(BpChildProxyClass *arg) { 
          return BpPrefixCompare(arg->GetName(), X());
	}    
    };
private:
    int    m_target_framework_id;
    string m_full_name;
}; // BpChildProxyClass

}

#endif /* BP_HIERARCHY_H */
