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

/*! \file ncsc/uvm_component_spec.cpp
  \brief OS specific uvm_component extensions.
*/

bool uvm_component::kill() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.kill();
  }
  return true;
}

bool uvm_component::reset() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.reset(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

bool uvm_component::suspend() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.suspend(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

bool uvm_component::resume() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.resume(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

bool uvm_component::disable() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.disable(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

bool uvm_component::enable() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.enable(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

bool uvm_component::sync_reset_on() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.sync_reset_on(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

bool uvm_component::sync_reset_off() {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.sync_reset_off(SC_INCLUDE_DESCENDANTS);
  }
  return true;
}

template <typename T>
bool uvm_component::throw_it(T& t) {
  if (m_run_handle.valid() && !m_run_handle.terminated()) {
    m_run_handle.throw_it(t, SC_INCLUDE_DESCENDANTS);
  }
  return true;
}
