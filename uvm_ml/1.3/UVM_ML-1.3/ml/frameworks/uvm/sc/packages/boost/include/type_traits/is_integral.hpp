
//  (C) Copyright Steve Cleary, Beman Dawes, Howard Hinnant & John Maddock 2000.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_IS_INTEGRAL_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_INTEGRAL_HPP_INCLUDED

#include <packages/boost/include/config.hpp>

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

//* is a type T an [cv-qualified-] integral type described in the standard (3.9.1p3)
// as an extention we include long long, as this is likely to be added to the
// standard at a later date
#if defined( __CODEGEARC__ )
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_integral,T,__is_integral(T))
#else
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_integral,T,false)

UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned char,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned short,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned int,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned long,true)

UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,signed char,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,signed short,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,signed int,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,signed long,true)

UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,bool,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,char,true)

#ifndef UVMSC_BOOST_NO_INTRINSIC_WCHAR_T
// If the following line fails to compile and you're using the Intel
// compiler, see http://lists.boost.org/MailArchives/boost-users/msg06567.php,
// and define UVMSC_BOOST_NO_INTRINSIC_WCHAR_T on the command line.
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,wchar_t,true)
#endif

// Same set of integral types as in packages/boost/include/type_traits/integral_promotion.hpp.
// Please, keep in sync. -- Alexander Nasonov
#if (defined(UVMSC_BOOST_MSVC) && (UVMSC_BOOST_MSVC < 1300)) \
    || (defined(UVMSC_BOOST_INTEL_CXX_VERSION) && defined(_MSC_VER) && (UVMSC_BOOST_INTEL_CXX_VERSION <= 600)) \
    || (defined(__BORLANDC__) && (__BORLANDC__ == 0x600) && (_MSC_VER < 1300))
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned __int8,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,__int8,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned __int16,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,__int16,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned __int32,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,__int32,true)
#ifdef __BORLANDC__
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned __int64,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,__int64,true)
#endif
#endif

# if defined(UVMSC_BOOST_HAS_LONG_LONG)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral, ::uvmsc_boost::ulong_long_type,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral, ::uvmsc_boost::long_long_type,true)
#elif defined(UVMSC_BOOST_HAS_MS_INT64)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,unsigned __int64,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_integral,__int64,true)
#endif

#endif  // non-CodeGear implementation

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_INTEGRAL_HPP_INCLUDED
