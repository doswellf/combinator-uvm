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

/*! @file bp_interconnect.h
 *
 *  Backplane Interconnect module header File
 * 
 *  Original Author: Vitaly Yankelevich, Cadence Design Systems, Inc.
 */

#ifndef BP_INTERCONNECT_H
#define BP_INTERCONNECT_H

#include <vector>
#include <string>
#include <assert.h>
#include "bp_utils.h"
#include "bp_framework_proxy.h"
#include "bp_connection.h"
#include "bp_c_interface.h"
#include "bp_type_map.h"
#include "bp_hierarchy.h"

using namespace std;

///////////

namespace Bp {

//! List of ptrs to the framework providing that service.
typedef struct frmw_srv_provider_struct
{
    FrameworkProxyClass * phase_srv_provider;   ///< ptr to phase service provider framework

} frmw_srv_provider_struct;


class BpTopDescriptorBaseClass;
class BpTopDescriptorClass;
class FrameworkProxyClass;

typedef int BpConnectionHandle;

//! Error handling function type; It should be provided by the master framework
typedef void  (bp_serror_t)(...);

//------------------------------------------------------------------------------
//! Enclosure class for backplane interface and global state.
/*! This class represents a singleton definition and contains only static members.
 *  It processes requests coming via the Backplane Provide API, 
 *  stores the ML hierarchy and connectivity information and re-directs the calls
 *  to the relevant frameworks.
 * 
 */
class BpInterconnect 
{

protected:

    //! Constructor
    BpInterconnect();

    //! Destructor
    ~BpInterconnect();

public:

    ////////////////////////////////////////////////////////////
    // Public Interface
    ////////////////////////////////////////////////////////////

    //-----------------------------------------------------------------------------
    //! Returns tray of Backplane provider API function pointers.
    /*!
     *  GetProvidedTray() shall be invoked first in order to obtain an access
     *  to BP Provided API
     */
    static bp_api_struct * GetProvidedTray();

    //-----------------------------------------------------------------------------
    //! Turn tracing on/off.
    /*! Each framework can invoke SetTraceMode() and BP broadcasts
     *  this request to turn on/off the UVM ML activities tracing
     */
    static void SetTraceMode(int mode);

    //-----------------------------------------------------------------------------
    //! Register a framework with the backplane.
    /*! Shall be invoked via the BP Provided API by each participating framework.
     *  It creates an internal framework proxy object in BP framework registry.
     *
     *  @param frameworkName - A voluntary string (ideally it shall be unique
     *              foreeach framework. This string is used only for tracing
     *
     *  @param frameworkIndicators - each framework shall be associated
     *              with one or more short string names (indicators). These 
     *              indicators are used by the integrator to denote the framework
     *
     *  @param requiredApi - a C function pointer array (BP Required API tray)
     *
     *  @return If successful - allocates and returns a unique FrameworkId
     *           (-1) - in case of an error
     */
    static int RegisterFramework(string &               frameworkName,
                                 vector<string> &       frameworkIndicators,
                                 bp_frmw_c_api_struct * requiredApi);

    //-----------------------------------------------------------------------------
    //! Process vector of strings that denotes top components/tests in TB.
    /*! Processes string arguments that denote ML hierarchy
     *  root nodes (components) and stores parsed values till the start of phasing.
     *
     *  UVM-ML supports multiple root nodes
     *
     *  @param tops  - a vector of strings, one per ML root node. Each top argument
     *                 shall follow the following pattern:
     *                 <Framework-indicator>:<Root-node-identifier>[:<Instance-name]
     *                 if instance-name is not specifies the root-node-identifier is 
     *                 duplicated as the instance name as well
     *  @param tests - a vector of strings, one per ML test identifier. A test is a 
     *                 root node with a predefined instance name (m_test_instance_name)
     *                 BP checks that not more than one test is specified.
     *                 BP issues an error if tests.size() > 1
     */
    static void ProcessTopsAndTests(vector<string> & tops, vector<string> & tests);


    //-----------------------------------------------------------------------------
    //! Allows a framework to add a root node descriptor procedurally 
    /*! (rather than as an argument of bp_run_test() or Bootstrap())
     *
     *  @param frameworkId    - the unique id previously allocated by RegisterFramework
     *  @param topComponentId - the root node id, unique for this framework only
     *  @param compIdentifier - the root node identifier string
     *  @param instanceName   - the root node instance name 
     *                          (to be used in a full hierarchical name)
     *
     *  @return The returns the following codes:
     *          - 1    : if the root node was added
     *          - 0    : if it was already registered before
     *          - (-1) : upon an error (if another root node was registered with the same instance name)
     */
    static int AddRootNode ( int            frameworkId, 
                             int            topComponentId,
                             const string & compIdentifier,
                             const string & instanceName);

    //-----------------------------------------------------------------------------
    //! Shall be invoked by a framework to connect ML TLM ports or sockets
    /*! (e.g. port<->export, initiator_socket<->target_socket)
     *
     *  @param frameworkId  - the unique id previously allocated by RegisterFramework
     *  @param producerPath - the full hierarchical name of a TLM1 
     *                        port/export or TLM2 initiator socket
     *  @param providerPath - the full hierarchical name of a TLM1 
     *                        export/imp or TLM2 target socket
     *
     *  @return Returns true upon success
     */
    static bool                   RegisterRoute(int         frameworkId, 
                                                string      producerPath,
                                                string      providerPath);

    //-----------------------------------------------------------------------------
    //! Notifies the framework of a non-runtime phase (non-time consuming).
    /*!
     *  Called by the master phase controller to notify a phase has started,
     *  is executing, is ready to end or has ended. 
     *  (from child to parent). 
     *
     *  @param frameworkId  - In the case of broadcasting, it's the unique ID 
     *                        of the master phase controller's framework adapter.
     *                        In the case where the notification is to a
     *                        particular component (targetId >= 0), it's 
     *                        the framework ID of the target component.
     *  @param phaseGroup   - Name of the group the phase belongs in 
     *                        (eg. common, uvm ...)
     *  @param phaseName    - Name of the phase
     *  @param phaseAction  - The action for this phase (start, execute,
     *                        ready to end, ended)
     *
     *  @return Return status
     *           - 1 : success
     *           - 0 : error
     */
    static int NotifyPhase(unsigned int        frameworkId,
                           const char *        phaseGroup,
                           const char *        phaseName,
                           uvm_ml_phase_action phaseAction);


    //-----------------------------------------------------------------------------
    //! Notifies a target component of a non_runtime phase (non-time conssuming).
    /*!
     *  Called by the backplane or child proxy to notify a phase.
     *
     *  @param frameworkId    - Unique ID of the framework adapter
     *  @param targetFrmwInd  - Framework indicator for the target
     *  @param targetId       - The ID of the target.
     *  @param phaseGroup     - Name of the group the phase belongs in 
     *                          (eg. common, uvm ...)
     *  @param phaseName      - Name of the phase
     *  @param phaseAction    - The action for this phase (start, execute,
     *                          ready to end, ended)
     *
     *  @return Return status
     *           - 1 : success
     *           - 0 : error
     */
    static int TransmitPhase(unsigned int        frameworkId,
                             const string &      targetFrmwInd,
                             int                 targetId,
                             const char *        phaseGroup,
                             const char *        phaseName,
                             uvm_ml_phase_action phaseAction);

    //-----------------------------------------------------------------------------
    //! Notifies the execution of a runtime phase.  A phase that consumes time.
    /*!
     *  Called by the master phase controller to notify a runtime phase 
     *  is executing. Unlike non-runtime phases which could execute either 
     *  topdown or bottom-up, a runtime phase is executed 'in parallel'.  
     *  The BpInterconnect will broadcast the phase to all framework only once,
     *  regardless of how many toplevel components the framework contains.
     *  The framework should phase all its' toplevel component at the same time.
     *  A framework could choose to participate in phase synchronization
     *  (controlling when the phase will end) by asserting the participate 
     *  variable.  The BpInterconnect will sum up the number of participating
     *  frameworks and pass the value back to the master phase controller.
     *  The framework notifies the phase master that it's 
     *  ready to exit the phase by calling bp_notify_phase_done().  The 
     *  master phase controller will wait until all participating frameworks
     *  are ready to exit the phase before continuing on to the next phase. 
     *
     *  @param frameworkId  - Unique ID of the framework adapter
     *  @param phaseGroup   - Name of the group the phase belongs in 
     *                        (eg. common, uvm ...)
     *  @param phaseName    - Name of the phase
     *  @param phaseAction  - The action for this phase (start, execute,
     *                        ready to end, ended)
     *  @param timeUnit     - Current simulation time unit
     *  @param timeValue    - Current simulatin time scaled according to timeUnit
     *  @param participate  - Indicates the number of frameworks participating 
     *                        in the phase
     *
     *  @return  Return status
     *           - 1 : success
     *           - 0 : error
     */
    static int NotifyRuntimePhase(unsigned int        frameworkId,
                                  const char *        phaseGroup,
                                  const char *        phaseName,
                                  uvm_ml_phase_action phaseAction,
                                  uvm_ml_time_unit    timeUnit,
                                  double              timeValue,
                                  unsigned int *      participate);

    //-----------------------------------------------------------------------------
    //! Notifies the phase master that the framework is ready to exit the phase.
    /*!
     *  @param frameworkId  - Unique ID of the framework adapter
     *  @param phaseGroup   - Name of the group the phase belongs in 
     *                        (eg. common, uvm ...)
     *  @param phaseName    - Name of the phase
     *  @param timeUnit     - Current simulation time unit
     *  @param timeValue    - Current simulatin time scaled according to time_unit
     */
    static void NotifyPhaseDone(unsigned int     frameworkId,
                                const char *     phaseGroup,
                                const char *     phaseName,
                                uvm_ml_time_unit timeUnit,
                                double           timeValue);

    //-----------------------------------------------------------------------------
    //! Calls the phase service provider to notify the framework is ready
    /*! to exit the phase.
     *
     *  @param frameworkId  - Unique ID of the framework adapter
     *  @param phaseGroup   - Name of the group the phase belongs in 
     *                        (eg. common, uvm ...)
     *  @param phaseName    - Name of the phase
     *  @param timeUnit     - Current simulation time unit
     *  @param timeValue    - Current simulatin time scaled according to time_unit
     */
    static void PhaseSrvNotifyPhaseDone(unsigned int      frameworkId,
                                        const char *      phaseGroup,
                                        const char *      phaseName,
                                        uvm_ml_time_unit  timeUnit,
                                        double            timeValue);

    //-----------------------------------------------------------------------------
    //! Calls the sevice provider to start phasing the ML TB. 
    //
    static void StartPhasing();

    //-----------------------------------------------------------------------------
    //! Register common service framework with backplane.
    /*!
     *  @param frmw  - Pointer to frameworkProxy
     */
    static void RegisterCommonSrvFrmw (FrameworkProxyClass * frmw);


    //-----------------------------------------------------------------------------
    //! Register service providers with the backplane.
    /*! Indicates to the backplane which services are being provided by
     *  which framework.  Could be call from the framework or the
     *  the user TB code.  All srv variables need not be filled.  Empty
     *  strings will be ignored.  If the same service is set multiple
     *  times, the last setting will be used.
     *
     *  @param frameworkId  - Unique ID of the framework adapter
     *  @param srvProviders - A struct containing variables
     *                        of type char * of all available 
     *                        services. Each variable 
     *                        specifies the name of the 
     *                        framework providing that service.
     */
    static void RegisterSrvProviders (unsigned int            frameworkId,
                                      bp_srv_provider_struct *srvProviders);


    //-----------------------------------------------------------------------------
    //! Returns the UVM-ML version.
    /*!
     *  @return The current UVM-ML version
     */
    static string GetVersion();


    ///////////////////////////////////////////////////////////////////////////////
    //                    TLM1 Core Interface methods
    ///////////////////////////////////////////////////////////////////////////////

    //-----------------------------------------------------------------------------
    //! TLM1 non-blocking put interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param streamSize      - size (in words) of the serialized transaction data stream
     *  @param stream          - serialized transaction data stream
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return The value returned by the export (imp)
     */
    static int                    NbPut(int              frameworkId,
                                        int              producerBindKey,
                                        unsigned int     streamSize,
                                        uvm_ml_stream_t  stream,
                                        uvm_ml_time_unit timeUnit,
                                        double           timeValue);

    //-----------------------------------------------------------------------------
    //! TLM1 non-blocking put interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return The value returned by the export (imp)
     */
    static int                    CanPut(int              frameworkId,
                                         int              producerBindKey,
                                         uvm_ml_time_unit timeUnit,
                                         double           timeValue);

    //-----------------------------------------------------------------------------
    //! TLM1 non-blocking get interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param streamSize      - return value: size (in words) of the serialized 
     *                           transaction data stream
     *  @param stream          - transaction data stream container to be filled by the export/imp
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return The value returned by the export (imp)
     */
    static int                    NbGet(int              frameworkId,
                                        int              producerBindKey,
                                        unsigned int &   streamSize,
                                        uvm_ml_stream_t  stream,
                                        uvm_ml_time_unit timeUnit,
                                        double           timeValue);
    //-----------------------------------------------------------------------------
    //! TLM1 non-blocking get interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return The value returned by the export (imp)
     */
    static int                    CanGet(int              frameworkId,
                                         int              producerBindKey,
                                         uvm_ml_time_unit timeUnit,
                                         double           timeValue);

    //-----------------------------------------------------------------------------
    //! TLM1 non-blocking peek interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param streamSize      - return value: size (in words) of the serialized transaction
     *                           data stream
     *  @param stream          - transaction data stream container to be filled by the export/imp
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return The value returned by the export (imp)
     */
    static int                    NbPeek(int              frameworkId,
                                         int              producerBindKey,
                                         unsigned int &   streamSize,
                                         uvm_ml_stream_t  stream,
                                         uvm_ml_time_unit timeUnit,
                                         double           timeValue);

    //-----------------------------------------------------------------------------
    //! TLM1 non-blocking peek interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return The value returned by the export (imp)
     */
    static int                    CanPeek(int              frameworkId,
                                          int              producerBindKey,
                                          uvm_ml_time_unit timeUnit,
                                          double           timeValue);

    //-----------------------------------------------------------------------------
    //! TLM analysis interface method
    /*!
     *  @param frameworkId     - the unique id previously allocated by RegisterFramework
     *  @param producerBindKey - a connection id on the producer's framework adapter side
     *  @param streamSize      - size (in words) of the serialized transaction data stream
     *  @param stream          - serialized transaction data stream
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     */
    static void                   Write(int              frameworkId,
                                        int              producerBindKey,
                                        unsigned int     streamSize,
                                        uvm_ml_stream_t  stream,
                                        uvm_ml_time_unit timeUnit,
                                        double           timeValue);

    //-----------------------------------------------------------------------------
    //! TLM1 blocking put interface method
    /*! This native blocking call is not supported
     *  The pseudo-blocking mechanism of RequestPut()/NotifyEndTask() shpild be used instead
     */
    static int                    Put(int                frameworkId,
                                      int                producerBindKey,
                                      unsigned int       streamSize,
                                      uvm_ml_stream_t    stream,
                                      uvm_ml_time_unit & timeUnit,
                                      double           & timeValue);

    //-----------------------------------------------------------------------------
    //! TLM! blocking put interface pseudo method.
    /*! Part of the pseudo-blocking mechanism for implementation of the 
     *  TLM1 blocking put interface method.
     *  This method spawns a thread (forks off a process) that can block through 
     *  a framework adapter. 
     *  When the process terminates the provider adapter invokes NotifyEndTask() and notifies 
     *  the producer adapter that the method completed.
     *
     *  @param frameworkId     - unique id previously allocated by RegisterFramework
     *  @param producerBindKey - connection id on the producer's framework adapter side
     *  @param requestId       - a unique id, assigned to this call by the producer 
     *                           framework adapter
     *  @param streamSize      - size (in words) of the serialized transaction data stream
     *  @param stream          - serialized transaction data stream
     *  @param done            - an output parameter; the provider adapter shall assign
     *                           it true if the call was  completed immediately (did not block)
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return Returns the following:
     *            - 0 : if the blocking calls completes normally
     *            - 1 : if the corresponding thread was disabled before normal completion
     */
    static int                    RequestPut(int                frameworkId,
                                             int                producerBindKey,
                                             int                requestId,
                                             unsigned int       streamSize,
                                             uvm_ml_stream_t    stream,
                                             bool &             done,
                                             uvm_ml_time_unit   timeUnit,
                                             double             timeValue);

    //-----------------------------------------------------------------------------
    //! TLM1 blocking get interface method
    /*! This native blocking call is not supported
     *  The pseudo-blocking mechanism of RequestGet()/NotifyEndTask() shpild be used instead
     */
    static int                    Get(int                frameworkId,
                                      int                producerBindKey,
                                      unsigned int &     streamSize,
                                      uvm_ml_stream_t    stream,
                                      uvm_ml_time_unit & timeUnit,
                                      double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Part of the pseudo-blocking mechanism for implementation of the TLM1 blocking
    /*! get interface method. This method spawns a thread (forks off a process) 
     *  that can block through the framework adapter. 
     *  When the process terminates the provider adapter invokes NotifyEndTask() and notifies the 
     *  producer adapter that the method completed.
     *
     *  @param frameworkId     - unique id previously allocated by RegisterFramework
     *  @param producerBindKey - connection id on the producer's framework adapter side
     *  @param requestId       - a unique id, assigned to this call by the producer 
     *                           framework adapter
     *  @param streamSize      - size (in words) of the returned serialized transaction 
     *                           data stream. The size value can be returned by this 
     *                           method only if the provider's get() implementation 
     *                           method returns immediately, without blocking
     *  @param stream          - container for returned serialized transaction data stream. 
     *                           It can be filled in this method only if the provider's 
     *                           get() implementation method returns immediately, 
     *                           without blocking
     *  @param done            - an output parameter; the provider adapter shall 
     *                           assign it true if the call was completed immediately 
     *                           (did not block)
     *  @param timeUnit        - current simulation time units enum (TIME_UNIT_UNDEFINED 
     *                           if the framework does not have an ability to advance time)
     *  @param timeValue       - numeric value of current simulation time scaled 
     *                           according to timeUnit
     *
     *  @return Returns the following:
     *          - 0 : if the blocking calls completes normally
     *          - 1 : if the corresponding thread was disabled before normal completion
     */
    static int                    RequestGet(int                frameworkId,
                                             int                producerBindKey,
                                             int                requestId,
                                             unsigned int &     streamSize,
                                             uvm_ml_stream_t    stream,
                                             bool &             done,
                                             uvm_ml_time_unit & timeUnit,
                                             double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Part of the pseudo-blocking mechanism for implementation of the TLM1 blocking 
    /*! get interface method. This method shall be invoked by the producer 
     *  framework's ML adapter after the thread spawned by Requestget() completes and 
     *  the provider framework ML adapter notifies the producer via NotifyEndTask().
     *
     *  @param frameworkId     - unique id previously allocated by RegisterFramework
     *  @param producerBindKey - connection id on the producer's framework adapter side
     *  @param requestId       - a unique id, assigned to this call by the producer 
     *                           framework adapter
     *  @param stream          - container for returned serialized transaction data
     *                           stream. It can be filled in this method only if the 
     *                           provider's get() implementation method returns 
     *                           immediately, without blocking
     *
     *  @return Output stream size
     */
    static unsigned int           GetRequested(int              frameworkId,
                                               int              producerBindKey,
                                               int              requestId,
                                               uvm_ml_stream_t  stream);

    //-----------------------------------------------------------------------------
    //! Native blocking call
    //
    static int                    Peek(int                frameworkId,
                                       int                producerBindKey,
                                       unsigned int &     streamSize,
                                       uvm_ml_stream_t    stream,
                                       uvm_ml_time_unit & timeUnit,
                                       double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Thread-spawning blocking call
    //
    static int                    RequestPeek(int                frameworkId,
                                              int                producerBindKey,
                                              int                requestId,
                                              unsigned int &     streamSize,
                                              uvm_ml_stream_t    stream,
                                              bool &             useTrueBlocking,
                                              uvm_ml_time_unit & timeUnit,
                                              double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Spawned blocking call completion
    //
    static unsigned int           PeekRequested(int              frameworkId,
                                                int              producerBindKey,
                                                int              requestId,
                                                uvm_ml_stream_t  stream);

    //-----------------------------------------------------------------------------
    //! Native blocking call
    //
    static int                    TransportTLM1(int                frameworkId,
                                                int                producerBindKey,
                                                unsigned int       reqStreamSize,
                                                uvm_ml_stream_t    reqStream,
                                                unsigned int     & respStreamSize,
                                                uvm_ml_stream_t  & respStream,
                                                uvm_ml_time_unit & timeUnit,
                                                double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Thread-spawning blocking call
    //
    static int                    RequestTransportTLM1(int                frameworkId,
                                                       int                producerBindKey,
                                                       int                requestId,
                                                       unsigned int       reqStreamSize,
                                                       uvm_ml_stream_t    reqStream,
                                                       unsigned int     & respStreamSize,
                                                       uvm_ml_stream_t  & respStream,
                                                       bool             & useTrueBlocking,
                                                       uvm_ml_time_unit & timeUnit,
                                                       double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Spawned blocking call completion
    /*!
     *  @return  RespStreamSize - response stream size
     */
    static int                    TransportTLM1Response(int               frameworkId,
                                                        int               producerBindKey,
                                                        int               requestId,
                                                        uvm_ml_stream_t & respStream);
    //
    static int                    NbTransportTLM1(int              frameworkId,
                                                  int              producerBindKey,
                                                  unsigned int     reqStreamSize,
                                                  uvm_ml_stream_t  reqStream,
                                                  unsigned int &   respStreamSize,
                                                  uvm_ml_stream_t  respStream,
                                                  uvm_ml_time_unit timeUnit,
                                                  double           timeValue);
    //
    static void                   NotifyEndBlocking(int              frameworkId,
                                                    int              requestId,
                                                    uvm_ml_time_unit timeUnit,
                                                    double           timeValue);
    

    ///////////////////////////////////////////////////////////////////////////////
    //                    TLM2 Interface methods
    ///////////////////////////////////////////////////////////////////////////////
    //

    //-----------------------------------------------------------------------------
    //! TLM2 blocking transport.
    //
    static int                    BTransportTLM2(int                frameworkId,
                                                 int                initiatorBindKey,
                                                 unsigned int     & streamSize,
                                                 uvm_ml_stream_t  & stream,
                                                 uvm_ml_time      & delay,
                                                 uvm_ml_time_unit & timeUnit,
                                                 double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Thread-spawning blocking call
    //
    static int                    RequestBTransportTLM2(int                frameworkId,
                                                        int                initiatorBindKey,
                                                        int                requestId,
                                                        unsigned int     & streamSize,
                                                        uvm_ml_stream_t  & stream,
                                                        uvm_ml_time      & delay,
                                                        bool             & useTrueBlocking,
                                                        uvm_ml_time_unit & timeUnit,
                                                        double           & timeValue);

    //-----------------------------------------------------------------------------
    //! Spawned blocking call completion
    /*!
     *  @return 0 if the task was disabled
     */
    static int                    BTransportTLM2Response(int               frameworkId,
                                                         int               initiatorBindKey,
                                                         int               requestId,
                                                         unsigned int    & streamSize,
                                                         uvm_ml_stream_t & stream);
    //
    static uvm_ml_tlm_sync_enum   NbTransportFwTLM2(int                frameworkId,
                                                    int                initiatorBindKey,
                                                    unsigned int     & streamSize,
                                                    uvm_ml_stream_t  & stream,
                                                    uvm_ml_tlm_phase & phase,
                                                    unsigned int       transactionId,
                                                    uvm_ml_time      & delay,
                                                    uvm_ml_time_unit   tImeUnit,
                                                    double             tImeValue);
    //
    static uvm_ml_tlm_sync_enum   NbTransportBwTLM2(int                frameworkId,
                                                    int                targetBindKey,
                                                    unsigned int     & streamSize,
                                                    uvm_ml_stream_t  & stream,
                                                    uvm_ml_tlm_phase & phase,
                                                    unsigned int       transactionId,
                                                    uvm_ml_time      & delay,
                                                    uvm_ml_time_unit   timeUnit,
                                                    double             timeValue);
    //
    static unsigned int           TransportDbgTLM2(int                frameworkId,
                                                   int                targetBindKey,
                                                   unsigned int     & streamSize,
                                                   uvm_ml_stream_t  & stream,
                                                   uvm_ml_time_unit   timeUnit,
                                                   double             timeValue);
    //
    static unsigned int           AssignTransactionId(int frameworkId);

    //
    static void                   TurnOffTransactionMapping(int      frameworkId,
                                                            string & socketName);

    ////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////////////////
    //                    Type Mapping API
    ///////////////////////////////////////////////////////////////////////////////
    //

    //-----------------------------------------------------------------------------
    //! May be used for transaction runtime type identification
    /*! Assuming that the connected frameworks support passing polymorphic transactions
     *  across the same TLM port/socket, the connected frameworks shall map the corresponding
     *  type names and obtain the unique type id from the bp. By default, the
     *  corresponding types are matched by name. Once the type id is obtained, 
     *  it shall be included by the producer/initiator in the transaction meta data 
     *  and the provider/target shall use the id to construct the correct object.
     */
    static uvm_ml_type_id_t       GetTypeIdByTypeName(int            frameworkId,
                                                      const string & typeName);

    //-----------------------------------------------------------------------------
    //! May be used by a framework if it supports passing polymorphic
    /*! transactions and needs a class name in order to construct the corresponding object
     *  on the provider/target side.
     */
    static string                 GetTypeNameByTypeId(int              frameworkId,
                                                      uvm_ml_type_id_t typeId,
                                                      bool             GetBaseName);
    

    //-----------------------------------------------------------------------------
    //! Allows explicit type mapping (default mapping is by the exact
    /*! type names match
     */
    static bool                   RegisterTypeMatch(BpLangTypeName & type1,
                                                    BpLangTypeName & type2);

    //////////////////////////////////////////////////////////// 

    /////////////////////////////////////////////////////////////////////////////// 
    //                    Resources and Configuration API
    //////////////////////////////////////////////////////////////////////////////////
    //

    //-----------------------------------------------------------------------------
    //! Configuration setting call
    //
    static void NotifyConfig(int              framework_id,
                             const char *     cntxt,
                             const char *     instance_name,
                             const char *     field_name,
                             unsigned int     stream_size,
                             uvm_ml_stream_t  stream,
                             uvm_ml_time_unit time_unit, 
                             double           time_value);


    ///////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////////////////
    //                    Connectivity Query API
    ///////////////////////////////////////////////////////////////////////////////
    //
    static BpConnectionHandle     FindConnectionHandle(int frameworkId,
                                                       int bindKey);

    static int                    QueryFanoutSize(BpConnectionHandle handle);

    static BpConnectionHandle     QueryFanoutHandle(BpConnectionHandle handle, unsigned int id);

    static int                    QueryFaninSize(BpConnectionHandle handle);

    static BpConnectionHandle     QueryFaninHandle(BpConnectionHandle handle, unsigned int id);

    static const string &         QueryFrameworkName(BpConnectionHandle handle);

    static const vector<string> & QueryFrameworkIndicators(BpConnectionHandle handle);

    static const string &         QueryConnectionPath(BpConnectionHandle handle);

    static int                    GetConnectorSize(int framework_id,int producer_id);

    ///////////////////////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////////////////
    //                    Time Synchronization Function
    /////////////////////////////////////////////////////////////////////////////// 
    static void Synchronize(int              framework_id, 
                            uvm_ml_time_unit timeUnit,
                            double           timeValue);

    static void Reset();
    //////////////////////////////////////////////////////////// 

    /////////////////////////////////////////////////////////////////////////////// 
    //                    ML Hierarchical Consruction and Phasing API
    /////////////////////////////////////////////////////////////////////////////// 

    static int CreateChildJunctionNode(int            frameworkId,
                                       const string & targetFrameworkIndicator,
                                       const string & componentTypeName,
                                       const string & instanceName,
                                       const string & parentFullName,
                                       int            parentJunctionNodeId);

    ///////////////////////////////////////////////////////////////////////////////
    //                    Optional Initialization API Functions
    ///////////////////////////////////////////////////////////////////////////////

    //-----------------------------------------------------------------------------
    //! Invoke phasing.
    /*! Is an optional method that can be invoked directly by a master simulator
     *  to start the phasing. This is an alternative mechanism to explicit phasing 
     *  initialization by the user(via the Provided API function bp_run_test). This 
     *  method allows to pass extra parameters, unsupported by bp_run_test().
     *
     *  @param preInitial - a function pointer that can be used to register a phasing start
     *                      callback. If used, it allows to execute the phasing before
     *                      execution of any user-defined inital blocks, processes, threads, etc.
     *  @param tops       - see ProcessTopsAndTests() description above 
     *  @param tests      - see ProcessTopsAndTests() description above 
     *  @param serror     - an optional function pointer that can be provided by a 
     *                      master simulator so that the simulator's messaging mechanism
     *                      can be used directly.
     *
     *  @return Returns the following :
     *          - if successful : the provided API function pointer array (tray)
     *          - 0 : upon an error
     */
    static bp_api_struct * Bootstrap( bp_preInitial_t * preInitial,
                                      vector<string>  & tops,
                                      vector<string>  & tests,
                                      bp_serror_t   *   serror);

    //-----------------------------------------------------------------------------
    //! Invoke phasing
    /*! This optional function may be invoked by a master simulator (e.g. as a pre-initial 
     *  callback function) to launch the pre-run phases
     *
     *  @return Returns the following :
     *          - 1 : upon success
     *          - 0 : if there was an elaboration time error
     */
    static int                    Elaborate(void *cbInfo);

public:

    ///////////////////////////////////////////////////////////////////////////////
    // Interconnect Implementation Services
    ///////////////////////////////////////////////////////////////////////////////
    //
    static void                       AddTopLevel (BpTopDescriptorClass * topComponent);
    //
    static FrameworkProxyClass *      GetFrameworkProxyByName(const string & frameworkName);
    //
    static FrameworkProxyClass *      GetFrameworkProxyByInd(const string frameworkIndicator);
    //
    static FrameworkProxyClass *      GetFramework(int frameworkId);
    //
    static BpConnectionClass *        FindConnectionByName(const string &path);
    //
    static BpConnectionClass *        AddConnection(string path);
    //
    static int                        GetTraceMode() { return m_trace_mode; }
    //
    static uvm_ml_type_id_t           GetUnregisteredTypeId(const string & typeName);
    //
    static const string &             FindUnregisteredTypeName(uvm_ml_type_id_t typeId);
    //
    static void                       AddRegisteredTypeEntry(BpTypeMapEntryClass * entry);
    //
    static uvm_ml_type_id_t           GetNextTypeId();
    //
    static BpConnectionClass *        GetSingleProvider(int frameworkId, int producerBindKey);
    //
    static BpConnectionClass *        GetSingleProducer(int frameworkId, int providerBindKey);
    //
    static bool                       FrameworksCompatibleBlocking(FrameworkProxyClass & frmw1, 
                                                                   FrameworkProxyClass & frmw2);
    //
    static void                       ParseArgument(const string & arg, // Input
                                       /* output */ string & frameworkIndicator,
                                                    string & compIdentifier, 
                                                    string & instanceName);
    //
    static void                       ParseTypeName(const string & arg, // Input
                                       /* output */ string & frameworkIndicator,
                                                    string & typeName);

    static void                       AddFrmwIndicator(string indicator, FrameworkProxyClass * frmw);


    static void                       SERROR(int msgId, string msg);
    static void                       SERROR2(int msgId, const char * fmt, string msg, string msg1);
    static void                       SERROR3(int msgId, const char * fmt, string msg, string msg1, string msg2);
    ////////////////////////////////////////////////////////////////////////////////

    //////
private:

    ////////////////////////////////////////////////////////////////////
    // 
    static bp_serror_t  *                                 m_serror;
    //
    static bp_api_struct                                  m_c_api_tray;
    //
    static vector< FrameworkProxyClass * >                *m_framework_registry_p;
    //
    static vector< FrameworkProxyClass * >&               GetFrameworkRegistry();
    //
    static vector< BpConnectionClass * >                  m_port_registry;
    //
    static vector< BpTopDescriptorClass * >               m_top_level_registry;
    //
    static vector< BpChildProxyClass * >                  m_child_proxy_registry;
    //
    static map<string /* FrameIndicator */, vector< FrameworkProxyClass * > * > *m_frameworks_by_ind_p;
    //
    static map<string /* FrameIndicator */, vector< FrameworkProxyClass * > * >& GetFrameworksByInd();
    static BpTopDescriptorClass *                                        m_test_component;
    //
    static int                                                           m_trace_mode;
    //
    static bool                                                          m_preInitial_cb_registered;
    //
    static bool                                                          m_elaboration_passed;
    //
    static int                                                           m_current_phase;
    //
    static string                                                        m_test_instance_name;
    //
    static map<string /* TypeName */, uvm_ml_type_id_t /* Type Id */ >   m_unregistered_types;
    //
    static map<uvm_ml_type_id_t /* Type Id */, string /* Type Name */ >  m_unregistered_type_names;
    //
    static vector <BpTypeMapEntryClass *>                  m_registered_types;
    //
    static vector< BpTopDescriptorBaseClass *>             m_top_arguments;
    //
    static uvm_ml_time                                     m_simulation_time;

    static frmw_srv_provider_struct   m_srv_providers;
    static FrameworkProxyClass *      m_common_frmw;

    ////////////////////////////////////////////////////////////////////

private:
    static void                       identifyTestComponent(string & arg);

    static void                       identifyTopComponent(string & arg);

    static void                       registerCBPreInitial(bp_preInitial_t * preInitial);

    static void                       fillCApiTray();

    static int                        initialize(void *cbInfo);

    static int                        addFramework(string &               frameworkName,
                                                   vector<string> &       frameworkIndicators,
                                                   bp_frmw_c_api_struct * requiredApi);

    static void                       setComponentFrameworks();

    static FrameworkProxyClass *      findFrameworkForPath(const string & path);
    static BpChildProxyClass *        findChildProxyforPath(const string & path);
    static bool                       checkAllConnections();
    static bool                       checkConnectionDirections(const BpConnectionClass & producer, 
                                                                const BpConnectionClass & provider);

    static void                       registerNewTypeMatch(FrameworkProxyClass * t1Frmw, 
                                                           const string &        t1Name, 
                                                           FrameworkProxyClass * t2Frmw, 
                                                           const string &        t2Name);

    static void                       mergeTypeEntries(BpTypeMapEntryClass * entry1, 
                                                       BpTypeMapEntryClass * entry2);

    static FrameworkProxyClass *      findServiceFrmw(const char * name);

    static void                       instantiateTop(BpTopDescriptorClass * top);

}; // class BpInterconnect


} // namespace Bp
#endif /* BP_INTERCONNECT_H */
