
// Copyright 2005-2009 Daniel James.
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#if !defined(UVMSC_BOOST_FUNCTIONAL_HASH_DETAIL_HASH_FLOAT_HEADER)
#define UVMSC_BOOST_FUNCTIONAL_HASH_DETAIL_HASH_FLOAT_HEADER

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

#include <packages/boost/include/config.hpp>
#include <packages/boost/include/functional/hash/detail/float_functions.hpp>
#include <packages/boost/include/functional/hash/detail/limits.hpp>
#include <packages/boost/include/integer/static_log2.hpp>
#include <packages/boost/include/cstdint.hpp>
#include <packages/boost/include/assert.hpp>

// Include hash implementation for the current platform.

// Cygwn
#if defined(__CYGWIN__)
#  if defined(__i386__) || defined(_M_IX86)
#    include <packages/boost/include/functional/hash/detail/hash_float_x86.hpp>
#  else
#    include <packages/boost/include/functional/hash/detail/hash_float_generic.hpp>
#  endif
#else
#  include <packages/boost/include/functional/hash/detail/hash_float_generic.hpp>
#endif

// Can we use fpclassify?

// STLport
#if defined(__SGI_STL_PORT) || defined(_STLPORT_VERSION)
#define UVMSC_BOOST_HASH_USE_FPCLASSIFY 0

// GNU libstdc++ 3
#elif defined(__GLIBCPP__) || defined(__GLIBCXX__)
#  if (defined(__USE_ISOC99) || defined(_GLIBCXX_USE_C99_MATH)) && \
      !(defined(macintosh) || defined(__APPLE__) || defined(__APPLE_CC__))
#    define UVMSC_BOOST_HASH_USE_FPCLASSIFY 1
#  else
#    define UVMSC_BOOST_HASH_USE_FPCLASSIFY 0
#  endif

// Everything else
#else
#  define UVMSC_BOOST_HASH_USE_FPCLASSIFY 0
#endif

#if UVMSC_BOOST_HASH_USE_FPCLASSIFY

#include <packages/boost/include/config/no_tr1/cmath.hpp>

namespace uvmsc_boost
{
    namespace hash_detail
    {
        template <class T>
        inline std::size_t float_hash_value(T v)
        {
            using namespace std;
            switch (fpclassify(v)) {
            case FP_ZERO:
                return 0;
            case FP_INFINITE:
                return (std::size_t)(v > 0 ? -1 : -2);
            case FP_NAN:
                return (std::size_t)(-3);
            case FP_NORMAL:
            case FP_SUBNORMAL:
                return float_hash_impl(v);
            default:
                UVMSC_BOOST_ASSERT(0);
                return 0;
            }
        }
    }
}

#else // !UVMSC_BOOST_HASH_USE_FPCLASSIFY

namespace uvmsc_boost
{
    namespace hash_detail
    {
        template <class T>
        inline std::size_t float_hash_value(T v)
        {
            return v == 0 ? 0 : float_hash_impl(v);
        }
    }
}

#endif // UVMSC_BOOST_HASH_USE_FPCLASSIFY

#undef UVMSC_BOOST_HASH_USE_FPCLASSIFY

#endif
