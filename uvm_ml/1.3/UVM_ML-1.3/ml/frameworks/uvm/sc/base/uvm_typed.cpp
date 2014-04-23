//----------------------------------------------------------------------
//   Copyright 2009 Cadence Design Systems, Inc.
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

/*! \file uvm_typed.cpp
  \brief Base class for typed UVM-SC objects.
*/

#include "base/uvm_typed.h"

using namespace std;

namespace uvm {

//------------------------------------------------------------------------------
//
// uvm_typed
//
//------------------------------------------------------------------------------

uvm_typed::uvm_typed() { }

uvm_typed::~uvm_typed() { }

string uvm_typed::get_type_name() const { return "uvm_typed"; }

} // namespace uvm
