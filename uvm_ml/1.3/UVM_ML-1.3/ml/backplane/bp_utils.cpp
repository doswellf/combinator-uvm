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

#include "bp_utils.h"

namespace Bp 
{

void * BpDlsym(const char * sym)
{
    static int   init = 0;
    static void *libHandle = NULL;

    if(!init) 
    {
        libHandle = dlopen(0, RTLD_LAZY | RTLD_GLOBAL);
        if(!libHandle) return NULL;
        init = 1;
    }
    return dlsym(libHandle, sym);
}

string BpExtractBaseName(const string & typeName)
{
    size_t pos = typeName.find_last_of(':');
    if (pos == string::npos) return typeName;
    else return typeName.substr(pos+1);
}

bool BpPrefixCompare(const string & prefixStr, const string & x)
{
    size_t prefix_len = prefixStr.length();
    size_t x_len = x.length();
    if ((prefix_len > x_len) || 
        ((prefix_len < x_len) && (x[prefix_len] != '.')))
        return false;

    return (x.compare(0, prefix_len, prefixStr, 0, prefix_len) == 0);
}

} // end namespace
