
//  (C) Copyright Steve Cleary, Beman Dawes, Howard Hinnant & John Maddock 2000.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_CONFIG_HPP_INCLUDED
#define UVMSC_BOOST_TT_CONFIG_HPP_INCLUDED

#ifndef UVMSC_BOOST_CONFIG_HPP
#include <packages/boost/include/config.hpp>
#endif

#include <packages/boost/include/detail/workaround.hpp>

//
// whenever we have a conversion function with elipses
// it needs to be declared __cdecl to suppress compiler
// warnings from MS and Borland compilers (this *must*
// appear before we include is_same.hpp below):
#if defined(UVMSC_BOOST_MSVC) || (defined(__BORLANDC__) && !defined(UVMSC_BOOST_DISABLE_WIN32))
#   define UVMSC_BOOST_TT_DECL __cdecl
#else
#   define UVMSC_BOOST_TT_DECL /**/
#endif

# if (UVMSC_BOOST_WORKAROUND(__MWERKS__, < 0x3000)                         \
    || UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1301)                        \
    || !defined(__EDG_VERSION__) && UVMSC_BOOST_WORKAROUND(__GNUC__, < 3) \
    || UVMSC_BOOST_WORKAROUND(__IBMCPP__, < 600 )                         \
    || UVMSC_BOOST_WORKAROUND(__BORLANDC__, < 0x5A0)                      \
    || defined(__ghs)                                               \
    || UVMSC_BOOST_WORKAROUND(__HP_aCC, < 60700)           \
    || UVMSC_BOOST_WORKAROUND(MPW_CPLUS, UVMSC_BOOST_TESTED_AT(0x890))          \
    || UVMSC_BOOST_WORKAROUND(__SUNPRO_CC, UVMSC_BOOST_TESTED_AT(0x580)))       \
    && defined(UVMSC_BOOST_NO_IS_ABSTRACT)

#   define UVMSC_BOOST_TT_NO_CONFORMING_IS_CLASS_IMPLEMENTATION 1

#endif

#ifndef UVMSC_BOOST_TT_NO_CONFORMING_IS_CLASS_IMPLEMENTATION
# define UVMSC_BOOST_TT_HAS_CONFORMING_IS_CLASS_IMPLEMENTATION 1
#endif

//
// Define UVMSC_BOOST_TT_NO_ELLIPSIS_IN_FUNC_TESTING 
// when we can't test for function types with elipsis:
//
#if UVMSC_BOOST_WORKAROUND(__GNUC__, < 3)
#  define UVMSC_BOOST_TT_NO_ELLIPSIS_IN_FUNC_TESTING
#endif

//
// define UVMSC_BOOST_TT_TEST_MS_FUNC_SIGS
// when we want to test __stdcall etc function types with is_function etc
// (Note, does not work with Borland, even though it does support __stdcall etc):
//
#if defined(_MSC_EXTENSIONS) && !defined(__BORLANDC__)
#  define UVMSC_BOOST_TT_TEST_MS_FUNC_SIGS
#endif

//
// define UVMSC_BOOST_TT_NO_CV_FUNC_TEST
// if tests for cv-qualified member functions don't 
// work in is_member_function_pointer
//
#if UVMSC_BOOST_WORKAROUND(__MWERKS__, < 0x3000) || UVMSC_BOOST_WORKAROUND(__IBMCPP__, <= 600)
#  define UVMSC_BOOST_TT_NO_CV_FUNC_TEST
#endif

#endif // UVMSC_BOOST_TT_CONFIG_HPP_INCLUDED


