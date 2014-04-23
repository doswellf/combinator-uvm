
//  (C) Copyright Steve Cleary, Beman Dawes, Howard Hinnant & John Maddock 2000.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_IS_ARITHMETIC_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_ARITHMETIC_HPP_INCLUDED

#if !defined( __CODEGEARC__ )
#include <packages/boost/include/type_traits/is_integral.hpp>
#include <packages/boost/include/type_traits/is_float.hpp>
#include <packages/boost/include/type_traits/detail/ice_or.hpp>
#include <packages/boost/include/config.hpp>
#endif

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

#if !defined(__CODEGEARC__)
namespace detail {

template< typename T >
struct is_arithmetic_impl
{ 
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = 
        (::uvmsc_boost::type_traits::ice_or< 
            ::uvmsc_boost::is_integral<T>::value,
            ::uvmsc_boost::is_float<T>::value
        >::value)); 
};

} // namespace detail
#endif

//* is a type T an arithmetic type described in the standard (3.9.1p8)
#if defined(__CODEGEARC__)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_arithmetic,T,__is_arithmetic(T))
#else
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_arithmetic,T,::uvmsc_boost::detail::is_arithmetic_impl<T>::value)
#endif

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_ARITHMETIC_HPP_INCLUDED
