
//  (C) Copyright John maddock 1999. 
//  (C) David Abrahams 2002.  Distributed under the Boost
//  Software License, Version 1.0. (See accompanying file
//  LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
//
// use this header as a workaround for missing <limits>

//  See http://www.boost.org/libs/compatibility/index.html for documentation.

#ifndef UVMSC_BOOST_LIMITS
#define UVMSC_BOOST_LIMITS

#include <packages/boost/include/config.hpp>

#ifdef UVMSC_BOOST_NO_LIMITS
# include <packages/boost/include/detail/limits.hpp>
#else
# include <limits>
#endif

#if (defined(UVMSC_BOOST_HAS_LONG_LONG) && defined(UVMSC_BOOST_NO_LONG_LONG_NUMERIC_LIMITS)) \
      || (defined(UVMSC_BOOST_HAS_MS_INT64) && defined(UVMSC_BOOST_NO_MS_INT64_NUMERIC_LIMITS))
// Add missing specializations for numeric_limits:
#ifdef UVMSC_BOOST_HAS_MS_INT64
#  define UVMSC_BOOST_LLT __int64
#  define UVMSC_BOOST_ULLT unsigned __int64
#else
#  define UVMSC_BOOST_LLT  ::uvmsc_boost::long_long_type
#  define UVMSC_BOOST_ULLT  ::uvmsc_boost::ulong_long_type
#endif

#include <climits>  // for CHAR_BIT

namespace std
{
  template<>
  class numeric_limits<UVMSC_BOOST_LLT> 
  {
   public:

      UVMSC_BOOST_STATIC_CONSTANT(bool, is_specialized = true);
#ifdef UVMSC_BOOST_HAS_MS_INT64
      static UVMSC_BOOST_LLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return 0x8000000000000000i64; }
      static UVMSC_BOOST_LLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return 0x7FFFFFFFFFFFFFFFi64; }
#elif defined(LLONG_MAX)
      static UVMSC_BOOST_LLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return LLONG_MIN; }
      static UVMSC_BOOST_LLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return LLONG_MAX; }
#elif defined(LONGLONG_MAX)
      static UVMSC_BOOST_LLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return LONGLONG_MIN; }
      static UVMSC_BOOST_LLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return LONGLONG_MAX; }
#else
      static UVMSC_BOOST_LLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return 1LL << (sizeof(UVMSC_BOOST_LLT) * CHAR_BIT - 1); }
      static UVMSC_BOOST_LLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return ~(min)(); }
#endif
      UVMSC_BOOST_STATIC_CONSTANT(int, digits = sizeof(UVMSC_BOOST_LLT) * CHAR_BIT -1);
      UVMSC_BOOST_STATIC_CONSTANT(int, digits10 = (CHAR_BIT * sizeof (UVMSC_BOOST_LLT) - 1) * 301L / 1000);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_signed = true);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_integer = true);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_exact = true);
      UVMSC_BOOST_STATIC_CONSTANT(int, radix = 2);
      static UVMSC_BOOST_LLT epsilon() throw() { return 0; };
      static UVMSC_BOOST_LLT round_error() throw() { return 0; };

      UVMSC_BOOST_STATIC_CONSTANT(int, min_exponent = 0);
      UVMSC_BOOST_STATIC_CONSTANT(int, min_exponent10 = 0);
      UVMSC_BOOST_STATIC_CONSTANT(int, max_exponent = 0);
      UVMSC_BOOST_STATIC_CONSTANT(int, max_exponent10 = 0);

      UVMSC_BOOST_STATIC_CONSTANT(bool, has_infinity = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_quiet_NaN = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_signaling_NaN = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_denorm = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_denorm_loss = false);
      static UVMSC_BOOST_LLT infinity() throw() { return 0; };
      static UVMSC_BOOST_LLT quiet_NaN() throw() { return 0; };
      static UVMSC_BOOST_LLT signaling_NaN() throw() { return 0; };
      static UVMSC_BOOST_LLT denorm_min() throw() { return 0; };

      UVMSC_BOOST_STATIC_CONSTANT(bool, is_iec559 = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_bounded = true);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_modulo = true);

      UVMSC_BOOST_STATIC_CONSTANT(bool, traps = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, tinyness_before = false);
      UVMSC_BOOST_STATIC_CONSTANT(float_round_style, round_style = round_toward_zero);
      
  };

  template<>
  class numeric_limits<UVMSC_BOOST_ULLT> 
  {
   public:

      UVMSC_BOOST_STATIC_CONSTANT(bool, is_specialized = true);
#ifdef UVMSC_BOOST_HAS_MS_INT64
      static UVMSC_BOOST_ULLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return 0ui64; }
      static UVMSC_BOOST_ULLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return 0xFFFFFFFFFFFFFFFFui64; }
#elif defined(ULLONG_MAX) && defined(ULLONG_MIN)
      static UVMSC_BOOST_ULLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return ULLONG_MIN; }
      static UVMSC_BOOST_ULLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return ULLONG_MAX; }
#elif defined(ULONGLONG_MAX) && defined(ULONGLONG_MIN)
      static UVMSC_BOOST_ULLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return ULONGLONG_MIN; }
      static UVMSC_BOOST_ULLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return ULONGLONG_MAX; }
#else
      static UVMSC_BOOST_ULLT min UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return 0uLL; }
      static UVMSC_BOOST_ULLT max UVMSC_BOOST_PREVENT_MACRO_SUBSTITUTION (){ return ~0uLL; }
#endif
      UVMSC_BOOST_STATIC_CONSTANT(int, digits = sizeof(UVMSC_BOOST_LLT) * CHAR_BIT);
      UVMSC_BOOST_STATIC_CONSTANT(int, digits10 = (CHAR_BIT * sizeof (UVMSC_BOOST_LLT)) * 301L / 1000);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_signed = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_integer = true);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_exact = true);
      UVMSC_BOOST_STATIC_CONSTANT(int, radix = 2);
      static UVMSC_BOOST_ULLT epsilon() throw() { return 0; };
      static UVMSC_BOOST_ULLT round_error() throw() { return 0; };

      UVMSC_BOOST_STATIC_CONSTANT(int, min_exponent = 0);
      UVMSC_BOOST_STATIC_CONSTANT(int, min_exponent10 = 0);
      UVMSC_BOOST_STATIC_CONSTANT(int, max_exponent = 0);
      UVMSC_BOOST_STATIC_CONSTANT(int, max_exponent10 = 0);

      UVMSC_BOOST_STATIC_CONSTANT(bool, has_infinity = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_quiet_NaN = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_signaling_NaN = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_denorm = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, has_denorm_loss = false);
      static UVMSC_BOOST_ULLT infinity() throw() { return 0; };
      static UVMSC_BOOST_ULLT quiet_NaN() throw() { return 0; };
      static UVMSC_BOOST_ULLT signaling_NaN() throw() { return 0; };
      static UVMSC_BOOST_ULLT denorm_min() throw() { return 0; };

      UVMSC_BOOST_STATIC_CONSTANT(bool, is_iec559 = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_bounded = true);
      UVMSC_BOOST_STATIC_CONSTANT(bool, is_modulo = true);

      UVMSC_BOOST_STATIC_CONSTANT(bool, traps = false);
      UVMSC_BOOST_STATIC_CONSTANT(bool, tinyness_before = false);
      UVMSC_BOOST_STATIC_CONSTANT(float_round_style, round_style = round_toward_zero);
      
  };
}
#endif 

#endif

