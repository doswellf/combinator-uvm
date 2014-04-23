
//  (C) Copyright Dave Abrahams, Steve Cleary, Beman Dawes, Howard
//  Hinnant & John Maddock 2000.  
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.


// Some fixes for is_array are based on a newgroup posting by Jonathan Lundquist.


#ifndef UVMSC_BOOST_TT_IS_ARRAY_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_ARRAY_HPP_INCLUDED

#include <packages/boost/include/type_traits/config.hpp>

#ifdef UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION
#   include <packages/boost/include/type_traits/detail/yes_no_type.hpp>
#   include <packages/boost/include/type_traits/detail/wrap.hpp>
#endif

#include <cstddef>

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

#if defined( __CODEGEARC__ )
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_array,T,__is_array(T))
#elif !defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_array,T,false)
#if !defined(UVMSC_BOOST_NO_ARRAY_TYPE_SPECIALIZATIONS)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,is_array,T[N],true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,is_array,T const[N],true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,is_array,T volatile[N],true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,is_array,T const volatile[N],true)
#if !UVMSC_BOOST_WORKAROUND(__BORLANDC__, < 0x600) && !defined(__IBMCPP__) &&  !UVMSC_BOOST_WORKAROUND(__DMC__, UVMSC_BOOST_TESTED_AT(0x840))
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_1(typename T,is_array,T[],true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_1(typename T,is_array,T const[],true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_1(typename T,is_array,T volatile[],true)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_1(typename T,is_array,T const volatile[],true)
#endif
#endif

#else // UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

namespace detail {

using ::uvmsc_boost::type_traits::yes_type;
using ::uvmsc_boost::type_traits::no_type;
using ::uvmsc_boost::type_traits::wrap;

template< typename T > T(* is_array_tester1(wrap<T>) )(wrap<T>);
char UVMSC_BOOST_TT_DECL is_array_tester1(...);

template< typename T> no_type is_array_tester2(T(*)(wrap<T>));
yes_type UVMSC_BOOST_TT_DECL is_array_tester2(...);

template< typename T >
struct is_array_impl
{ 
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = 
        sizeof(::uvmsc_boost::detail::is_array_tester2(
            ::uvmsc_boost::detail::is_array_tester1(
                ::uvmsc_boost::type_traits::wrap<T>()
                )
        )) == 1
    );
};

#ifndef UVMSC_BOOST_NO_CV_VOID_SPECIALIZATIONS
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_IMPL_SPEC1(is_array,void,false)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_IMPL_SPEC1(is_array,void const,false)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_IMPL_SPEC1(is_array,void volatile,false)
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_IMPL_SPEC1(is_array,void const volatile,false)
#endif

} // namespace detail

UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_array,T,::uvmsc_boost::detail::is_array_impl<T>::value)

#endif // UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_ARRAY_HPP_INCLUDED
