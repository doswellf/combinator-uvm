
//  (C) Copyright Dave Abrahams, Steve Cleary, Beman Dawes, 
//      Howard Hinnant and John Maddock 2000, 2010. 
//  (C) Copyright Mat Marcus, Jesse Jones and Adobe Systems Inc 2001

//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_IS_REFERENCE_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_REFERENCE_HPP_INCLUDED

#include <packages/boost/include/type_traits/config.hpp>
#include <packages/boost/include/type_traits/is_lvalue_reference.hpp>
#include <packages/boost/include/type_traits/is_rvalue_reference.hpp>
#include <packages/boost/include/type_traits/ice.hpp>

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

namespace detail {

template <typename T>
struct is_reference_impl
{
   UVMSC_BOOST_STATIC_CONSTANT(bool, value =
      (::uvmsc_boost::type_traits::ice_or<
         ::uvmsc_boost::is_lvalue_reference<T>::value, ::uvmsc_boost::is_rvalue_reference<T>::value
       >::value));
};

} // namespace detail

UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_reference,T,::uvmsc_boost::detail::is_reference_impl<T>::value)

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_REFERENCE_HPP_INCLUDED

