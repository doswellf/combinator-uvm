// Copyright David Abrahams 2002.
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
#ifndef UVMSC_BOOST_WORKAROUND_DWA2002126_HPP
# define UVMSC_BOOST_WORKAROUND_DWA2002126_HPP

// Compiler/library version workaround macro
//
// Usage:
//
//     #if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, < 1300)
//        // workaround for eVC4 and VC6
//        ... // workaround code here
//     #endif
//
// When UVMSC_BOOST_STRICT_CONFIG is defined, expands to 0. Otherwise, the
// first argument must be undefined or expand to a numeric
// value. The above expands to:
//
//     (UVMSC_BOOST_MSVC) != 0 && (UVMSC_BOOST_MSVC) < 1300
//
// When used for workarounds that apply to the latest known version 
// and all earlier versions of a compiler, the following convention 
// should be observed:
//
//     #if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, UVMSC_BOOST_TESTED_AT(1301))
//
// The version number in this case corresponds to the last version in
// which the workaround was known to have been required. When
// UVMSC_BOOST_DETECT_OUTDATED_WORKAROUNDS is not the defined, the macro
// UVMSC_BOOST_TESTED_AT(x) expands to "!= 0", which effectively activates
// the workaround for any version of the compiler. When
// UVMSC_BOOST_DETECT_OUTDATED_WORKAROUNDS is defined, a compiler warning or
// error will be issued if the compiler version exceeds the argument
// to UVMSC_BOOST_TESTED_AT().  This can be used to locate workarounds which
// may be obsoleted by newer versions.

# ifndef UVMSC_BOOST_STRICT_CONFIG

#include <packages/boost/include/config.hpp>

#ifndef __BORLANDC__
#define __BORLANDC___WORKAROUND_GUARD 1
#else
#define __BORLANDC___WORKAROUND_GUARD 0
#endif
#ifndef __CODEGEARC__
#define __CODEGEARC___WORKAROUND_GUARD 1
#else
#define __CODEGEARC___WORKAROUND_GUARD 0
#endif
#ifndef _MSC_VER
#define _MSC_VER_WORKAROUND_GUARD 1
#else
#define _MSC_VER_WORKAROUND_GUARD 0
#endif
#ifndef _MSC_FULL_VER
#define _MSC_FULL_VER_WORKAROUND_GUARD 1
#else
#define _MSC_FULL_VER_WORKAROUND_GUARD 0
#endif
#ifndef UVMSC_BOOST_MSVC
#define UVMSC_BOOST_MSVC_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_MSVC_WORKAROUND_GUARD 0
#endif
#ifndef UVMSC_BOOST_MSVC_FULL_VER
#define UVMSC_BOOST_MSVC_FULL_VER_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_MSVC_FULL_VER_WORKAROUND_GUARD 0
#endif
#ifndef __GNUC__
#define __GNUC___WORKAROUND_GUARD 1
#else
#define __GNUC___WORKAROUND_GUARD 0
#endif
#ifndef __GNUC_MINOR__
#define __GNUC_MINOR___WORKAROUND_GUARD 1
#else
#define __GNUC_MINOR___WORKAROUND_GUARD 0
#endif
#ifndef __GNUC_PATCHLEVEL__
#define __GNUC_PATCHLEVEL___WORKAROUND_GUARD 1
#else
#define __GNUC_PATCHLEVEL___WORKAROUND_GUARD 0
#endif
#ifndef __IBMCPP__
#define __IBMCPP___WORKAROUND_GUARD 1
#else
#define __IBMCPP___WORKAROUND_GUARD 0
#endif
#ifndef __SUNPRO_CC
#define __SUNPRO_CC_WORKAROUND_GUARD 1
#else
#define __SUNPRO_CC_WORKAROUND_GUARD 0
#endif
#ifndef __DECCXX_VER
#define __DECCXX_VER_WORKAROUND_GUARD 1
#else
#define __DECCXX_VER_WORKAROUND_GUARD 0
#endif
#ifndef __MWERKS__
#define __MWERKS___WORKAROUND_GUARD 1
#else
#define __MWERKS___WORKAROUND_GUARD 0
#endif
#ifndef __EDG__
#define __EDG___WORKAROUND_GUARD 1
#else
#define __EDG___WORKAROUND_GUARD 0
#endif
#ifndef __EDG_VERSION__
#define __EDG_VERSION___WORKAROUND_GUARD 1
#else
#define __EDG_VERSION___WORKAROUND_GUARD 0
#endif
#ifndef __HP_aCC
#define __HP_aCC_WORKAROUND_GUARD 1
#else
#define __HP_aCC_WORKAROUND_GUARD 0
#endif
#ifndef __hpxstd98
#define __hpxstd98_WORKAROUND_GUARD 1
#else
#define __hpxstd98_WORKAROUND_GUARD 0
#endif
#ifndef _CRAYC
#define _CRAYC_WORKAROUND_GUARD 1
#else
#define _CRAYC_WORKAROUND_GUARD 0
#endif
#ifndef __DMC__
#define __DMC___WORKAROUND_GUARD 1
#else
#define __DMC___WORKAROUND_GUARD 0
#endif
#ifndef MPW_CPLUS
#define MPW_CPLUS_WORKAROUND_GUARD 1
#else
#define MPW_CPLUS_WORKAROUND_GUARD 0
#endif
#ifndef __COMO__
#define __COMO___WORKAROUND_GUARD 1
#else
#define __COMO___WORKAROUND_GUARD 0
#endif
#ifndef __COMO_VERSION__
#define __COMO_VERSION___WORKAROUND_GUARD 1
#else
#define __COMO_VERSION___WORKAROUND_GUARD 0
#endif
#ifndef __INTEL_COMPILER
#define __INTEL_COMPILER_WORKAROUND_GUARD 1
#else
#define __INTEL_COMPILER_WORKAROUND_GUARD 0
#endif
#ifndef __ICL
#define __ICL_WORKAROUND_GUARD 1
#else
#define __ICL_WORKAROUND_GUARD 0
#endif
#ifndef _COMPILER_VERSION
#define _COMPILER_VERSION_WORKAROUND_GUARD 1
#else
#define _COMPILER_VERSION_WORKAROUND_GUARD 0
#endif

#ifndef _RWSTD_VER
#define _RWSTD_VER_WORKAROUND_GUARD 1
#else
#define _RWSTD_VER_WORKAROUND_GUARD 0
#endif
#ifndef UVMSC_BOOST_RWSTD_VER
#define UVMSC_BOOST_RWSTD_VER_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_RWSTD_VER_WORKAROUND_GUARD 0
#endif
#ifndef __GLIBCPP__
#define __GLIBCPP___WORKAROUND_GUARD 1
#else
#define __GLIBCPP___WORKAROUND_GUARD 0
#endif
#ifndef _GLIBCXX_USE_C99_FP_MACROS_DYNAMIC
#define _GLIBCXX_USE_C99_FP_MACROS_DYNAMIC_WORKAROUND_GUARD 1
#else
#define _GLIBCXX_USE_C99_FP_MACROS_DYNAMIC_WORKAROUND_GUARD 0
#endif
#ifndef __SGI_STL_PORT
#define __SGI_STL_PORT_WORKAROUND_GUARD 1
#else
#define __SGI_STL_PORT_WORKAROUND_GUARD 0
#endif
#ifndef _STLPORT_VERSION
#define _STLPORT_VERSION_WORKAROUND_GUARD 1
#else
#define _STLPORT_VERSION_WORKAROUND_GUARD 0
#endif
#ifndef __LIBCOMO_VERSION__
#define __LIBCOMO_VERSION___WORKAROUND_GUARD 1
#else
#define __LIBCOMO_VERSION___WORKAROUND_GUARD 0
#endif
#ifndef _CPPLIB_VER
#define _CPPLIB_VER_WORKAROUND_GUARD 1
#else
#define _CPPLIB_VER_WORKAROUND_GUARD 0
#endif

#ifndef UVMSC_BOOST_INTEL_CXX_VERSION
#define UVMSC_BOOST_INTEL_CXX_VERSION_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_INTEL_CXX_VERSION_WORKAROUND_GUARD 0
#endif
#ifndef UVMSC_BOOST_INTEL_WIN
#define UVMSC_BOOST_INTEL_WIN_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_INTEL_WIN_WORKAROUND_GUARD 0
#endif
#ifndef UVMSC_BOOST_DINKUMWARE_STDLIB
#define UVMSC_BOOST_DINKUMWARE_STDLIB_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_DINKUMWARE_STDLIB_WORKAROUND_GUARD 0
#endif
#ifndef UVMSC_BOOST_INTEL
#define UVMSC_BOOST_INTEL_WORKAROUND_GUARD 1
#else
#define UVMSC_BOOST_INTEL_WORKAROUND_GUARD 0
#endif
// Always define to zero, if it's used it'll be defined my MPL:
#define UVMSC_BOOST_MPL_CFG_GCC_WORKAROUND_GUARD 0

#  define UVMSC_BOOST_WORKAROUND(symbol, test)                \
         ((symbol ## _WORKAROUND_GUARD + 0 == 0) &&     \
         (symbol != 0) && (1 % (( (symbol test) ) + 1)))
//                              ^ ^           ^ ^
// The extra level of parenthesis nesting above, along with the
// UVMSC_BOOST_OPEN_PAREN indirection below, is required to satisfy the
// broken preprocessor in MWCW 8.3 and earlier.
//
// The basic mechanism works as follows:
//      (symbol test) + 1        =>   if (symbol test) then 2 else 1
//      1 % ((symbol test) + 1)  =>   if (symbol test) then 1 else 0
//
// The complication with % is for cooperation with UVMSC_BOOST_TESTED_AT().
// When "test" is UVMSC_BOOST_TESTED_AT(x) and
// UVMSC_BOOST_DETECT_OUTDATED_WORKAROUNDS is #defined,
//
//      symbol test              =>   if (symbol <= x) then 1 else -1
//      (symbol test) + 1        =>   if (symbol <= x) then 2 else 0
//      1 % ((symbol test) + 1)  =>   if (symbol <= x) then 1 else divide-by-zero
//

#  ifdef UVMSC_BOOST_DETECT_OUTDATED_WORKAROUNDS
#   define UVMSC_BOOST_OPEN_PAREN (
#   define UVMSC_BOOST_TESTED_AT(value)  > value) ?(-1): UVMSC_BOOST_OPEN_PAREN 1
#  else
#   define UVMSC_BOOST_TESTED_AT(value) != ((value)-(value))
#  endif

# else

#  define UVMSC_BOOST_WORKAROUND(symbol, test) 0

# endif 

#endif // UVMSC_BOOST_WORKAROUND_DWA2002126_HPP
