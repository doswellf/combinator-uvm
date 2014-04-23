
//  (C) Copyright Steve Cleary, Beman Dawes, Howard Hinnant & John Maddock 2000.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_IS_VOID_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_VOID_HPP_INCLUDED

#include <packages/boost/include/config.hpp>

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

//* is a type T void - is_void<T>
#if defined( __CODEGEARC__ )
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_void,T,__is_void(T))
#else
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_void,T,false)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_SPEC1(is_void,void,true)

#ifndef UVMSC_BOOST_NO_CV_VOID_SPECIALIZATIONS
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_SPEC1(is_void,void const,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_SPEC1(is_void,void volatile,true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_SPEC1(is_void,void const volatile,true)
#endif

#endif  // non-CodeGear implementation

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_VOID_HPP_INCLUDED
