
//  (C) Copyright Steve Cleary, Beman Dawes, Howard Hinnant & John Maddock 2000.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TYPE_TRAITS_IS_FLOAT_HPP_INCLUDED
#define UVMSC_BOOST_TYPE_TRAITS_IS_FLOAT_HPP_INCLUDED

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

//* is a type T a floating-point type described in the standard (3.9.1p8)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_float,T,false)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_float,float,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_float,double,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_CV_SPEC1(is_float,long double,true)

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TYPE_TRAITS_IS_FLOAT_HPP_INCLUDED
