
// Copyright 2005-2011 Daniel James.
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

// Note: if you change this include guard, you also need to change
// container_fwd_compile_fail.cpp
#if !defined(UVMSC_BOOST_DETAIL_CONTAINER_FWD_HPP)
#define UVMSC_BOOST_DETAIL_CONTAINER_FWD_HPP

#if defined(_MSC_VER) && (_MSC_VER >= 1020) && \
    !defined(UVMSC_BOOST_DETAIL_TEST_CONFIG_ONLY)
# pragma once
#endif

#include <packages/boost/include/config.hpp>
#include <packages/boost/include/detail/workaround.hpp>

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD if you don't want this header to      //
// forward declare standard containers.                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#if !defined(UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD)
#  if defined(__SGI_STL_PORT) || defined(_STLPORT_VERSION)
     // STLport
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  elif defined(__LIBCOMO__)
     // Comeau STL:
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  elif defined(__STD_RWCOMPILER_H__) || defined(_RWSTD_VER)
     // Rogue Wave library:
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  elif defined(_LIBCPP_VERSION)
     // libc++
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  elif defined(__GLIBCPP__) || defined(__GLIBCXX__)
     // GNU libstdc++ 3
     //
     // Disable forwarding for all recent versions, as the library has a
     // versioned namespace mode, and I don't know how to detect it.
#    if __GLIBCXX__ >= 20070513 \
        || defined(_GLIBCXX_DEBUG) \
        || defined(_GLIBCXX_PARALLEL) \
        || defined(_GLIBCXX_PROFILE)
#      define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#    else
#      if defined(__GLIBCXX__) && __GLIBCXX__ >= 20040530
#        define UVMSC_BOOST_CONTAINER_FWD_COMPLEX_STRUCT
#      endif
#    endif
#  elif defined(__STL_CONFIG_H)
     // generic SGI STL
     //
     // Forward declaration seems to be okay, but it has a couple of odd
     // implementations.
#    define UVMSC_BOOST_CONTAINER_FWD_BAD_BITSET
#    if !defined(__STL_NON_TYPE_TMPL_PARAM_BUG)
#      define UVMSC_BOOST_CONTAINER_FWD_BAD_DEQUE
#     endif
#  elif defined(__MSL_CPP__)
     // MSL standard lib:
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  elif defined(__IBMCPP__)
     // The default VACPP std lib, forward declaration seems to be fine.
#  elif defined(MSIPL_COMPILE_H)
     // Modena C++ standard library
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  elif (defined(_YVALS) && !defined(__IBMCPP__)) || defined(_CPPLIB_VER)
     // Dinkumware Library (this has to appear after any possible replacement
     // libraries)
#  else
#    define UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD
#  endif
#endif

// UVMSC_BOOST_DETAIL_TEST_* macros are for testing only
// and shouldn't be relied upon. But you can use
// UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD to prevent forward
// declaration of containers.

#if !defined(UVMSC_BOOST_DETAIL_TEST_CONFIG_ONLY)

#if defined(UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD) && \
    !defined(UVMSC_BOOST_DETAIL_TEST_FORCE_CONTAINER_FWD)

#include <deque>
#include <list>
#include <vector>
#include <map>
#include <set>
#include <bitset>
#include <string>
#include <complex>

#else

#include <cstddef>

#if defined(UVMSC_BOOST_CONTAINER_FWD_BAD_DEQUE)
#include <deque>
#endif

#if defined(UVMSC_BOOST_CONTAINER_FWD_BAD_BITSET)
#include <bitset>
#endif

#if defined(UVMSC_BOOST_MSVC)
#pragma warning(push)
#pragma warning(disable:4099) // struct/class mismatch in fwd declarations
#endif

namespace std
{
    template <class T> class allocator;
    template <class charT, class traits, class Allocator> class basic_string;

#if UVMSC_BOOST_WORKAROUND(__GNUC__, < 3) && !defined(__SGI_STL_PORT) && !defined(_STLPORT_VERSION)
    template <class charT> struct string_char_traits;
#else
    template <class charT> struct char_traits;
#endif

#if defined(UVMSC_BOOST_CONTAINER_FWD_COMPLEX_STRUCT)
    template <class T> struct complex;
#else
    template <class T> class complex;
#endif

#if !defined(UVMSC_BOOST_CONTAINER_FWD_BAD_DEQUE)
    template <class T, class Allocator> class deque;
#endif

    template <class T, class Allocator> class list;
    template <class T, class Allocator> class vector;
    template <class Key, class T, class Compare, class Allocator> class map;
    template <class Key, class T, class Compare, class Allocator>
    class multimap;
    template <class Key, class Compare, class Allocator> class set;
    template <class Key, class Compare, class Allocator> class multiset;

#if !defined(UVMSC_BOOST_CONTAINER_FWD_BAD_BITSET)
    template <size_t N> class bitset;
#endif
    template <class T1, class T2> struct pair;
}

#if defined(UVMSC_BOOST_MSVC)
#pragma warning(pop)
#endif

#endif // UVMSC_BOOST_DETAIL_NO_CONTAINER_FWD &&
       // !defined(UVMSC_BOOST_DETAIL_TEST_FORCE_CONTAINER_FWD)

#endif // UVMSC_BOOST_DETAIL_TEST_CONFIG_ONLY

#endif
