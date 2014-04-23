
//  Copyright 2001-2003 Aleksey Gurtovoy.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC_HPP_INCLUDED
#define UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC_HPP_INCLUDED

#include <packages/boost/include/mpl/aux_/lambda_support.hpp>
#include <packages/boost/include/config.hpp>

// these are needed regardless of UVMSC_BOOST_TT_NO_BROKEN_COMPILER_SPEC 
#if defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION)
namespace uvmsc_boost { namespace detail {
template< typename T > struct remove_const_impl     { typedef T type; };
template< typename T > struct remove_volatile_impl  { typedef T type; };
template< typename T > struct remove_pointer_impl   { typedef T type; };
template< typename T > struct remove_reference_impl { typedef T type; };
typedef int invoke_UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC_outside_all_namespaces;
}}
#endif

// agurt, 27/jun/03: disable the workaround if user defined 
// UVMSC_BOOST_TT_NO_BROKEN_COMPILER_SPEC
#if    !defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION) \
    || defined(UVMSC_BOOST_TT_NO_BROKEN_COMPILER_SPEC)

#   define UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(T) /**/

#else

// same as UVMSC_BOOST_TT_AUX_TYPE_TRAIT_IMPL_SPEC1 macro, except that it
// never gets #undef-ined
#   define UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(trait,spec,result) \
template<> struct trait##_impl<spec> \
{ \
    typedef result type; \
}; \
/**/

#   define UVMSC_BOOST_TT_AUX_REMOVE_CONST_VOLATILE_RANK1_SPEC(T)                         \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_const,T const,T)                    \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_const,T const volatile,T volatile)  \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_volatile,T volatile,T)              \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_volatile,T const volatile,T const)  \
    /**/

#   define UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_1_SPEC(T)                               \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_pointer,T*,T)                       \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_pointer,T*const,T)                  \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_pointer,T*volatile,T)               \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_pointer,T*const volatile,T)         \
    UVMSC_BOOST_TT_AUX_BROKEN_TYPE_TRAIT_SPEC1(remove_reference,T&,T)                     \
    /**/

#   define UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_2_SPEC(T)                               \
    UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_1_SPEC(T)                                      \
    UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_1_SPEC(T const)                                \
    UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_1_SPEC(T volatile)                             \
    UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_1_SPEC(T const volatile)                       \
    /**/

#   define UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_1_SPEC(T)                                   \
    UVMSC_BOOST_TT_AUX_REMOVE_PTR_REF_RANK_2_SPEC(T)                                      \
    UVMSC_BOOST_TT_AUX_REMOVE_CONST_VOLATILE_RANK1_SPEC(T)                                \
    /**/

#   define UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_2_SPEC(T)                                   \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_1_SPEC(T*)                                         \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_1_SPEC(T const*)                                   \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_1_SPEC(T volatile*)                                \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_1_SPEC(T const volatile*)                          \
    /**/

#   define UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(T)                                         \
    namespace uvmsc_boost { namespace detail {                                            \
    typedef invoke_UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC_outside_all_namespaces             \
      please_invoke_UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC_outside_all_namespaces;           \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_1_SPEC(T)                                          \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_2_SPEC(T)                                          \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_2_SPEC(T*)                                         \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_2_SPEC(T const*)                                   \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_2_SPEC(T volatile*)                                \
    UVMSC_BOOST_TT_AUX_REMOVE_ALL_RANK_2_SPEC(T const volatile*)                          \
    }}                                                                              \
    /**/

#   include <packages/boost/include/type_traits/detail/type_trait_undef.hpp>

#endif // UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(bool)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(char)
#ifndef UVMSC_BOOST_NO_INTRINSIC_WCHAR_T
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(wchar_t)
#endif
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(signed char)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(unsigned char)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(signed short)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(unsigned short)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(signed int)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(unsigned int)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(signed long)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(unsigned long)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(float)
UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(double)
//UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(long double)

// for backward compatibility
#define UVMSC_BOOST_BROKEN_COMPILER_TYPE_TRAITS_SPECIALIZATION(T) \
    UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC(T) \
/**/

#endif // UVMSC_BOOST_TT_BROKEN_COMPILER_SPEC_HPP_INCLUDED
