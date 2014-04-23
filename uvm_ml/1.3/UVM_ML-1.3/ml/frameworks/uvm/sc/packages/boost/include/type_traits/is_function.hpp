
//  Copyright 2000 John Maddock (john@johnmaddock.co.uk)
//  Copyright 2002 Aleksey Gurtovoy (agurtovoy@meta-comm.com)
//
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_IS_FUNCTION_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_FUNCTION_HPP_INCLUDED

#include <packages/boost/include/type_traits/is_reference.hpp>
#include <packages/boost/include/type_traits/detail/false_result.hpp>
#include <packages/boost/include/config.hpp>

#if !defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION) && !defined(UVMSC_BOOST_TT_TEST_MS_FUNC_SIGS)
#   include <packages/boost/include/type_traits/detail/is_function_ptr_helper.hpp>
#else
#   include <packages/boost/include/type_traits/detail/is_function_ptr_tester.hpp>
#   include <packages/boost/include/type_traits/detail/yes_no_type.hpp>
#endif

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

// is a type a function?
// Please note that this implementation is unnecessarily complex:
// we could just use !is_convertible<T*, const volatile void*>::value,
// except that some compilers erroneously allow conversions from
// function pointers to void*.

namespace uvmsc_boost {

#if !defined( __CODEGEARC__ )

namespace detail {

#if !defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION) && !defined(UVMSC_BOOST_TT_TEST_MS_FUNC_SIGS)
template<bool is_ref = true>
struct is_function_chooser
    : public ::uvmsc_boost::type_traits::false_result
{
};

template <>
struct is_function_chooser<false>
{
    template< typename T > struct result_
        : public ::uvmsc_boost::type_traits::is_function_ptr_helper<T*>
    {
    };
};

template <typename T>
struct is_function_impl
    : public is_function_chooser< ::uvmsc_boost::is_reference<T>::value >
        ::UVMSC_BOOST_NESTED_TEMPLATE result_<T>
{
};

#else

template <typename T>
struct is_function_impl
{
#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC_FULL_VER, >= 140050000)
#pragma warning(push)
#pragma warning(disable:6334)
#endif
    static T* t;
    UVMSC_BOOST_STATIC_CONSTANT(
        bool, value = sizeof(::uvmsc_boost::type_traits::is_function_ptr_tester(t))
        == sizeof(::uvmsc_boost::type_traits::yes_type)
        );
#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC_FULL_VER, >= 140050000)
#pragma warning(pop)
#endif
};

#if !defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION)
template <typename T>
struct is_function_impl<T&> : public false_type
{};
#endif

#endif

} // namespace detail

#endif // !defined( __CODEGEARC__ )

#if defined( __CODEGEARC__ )
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_function,T,__is_function(T))
#else
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_function,T,::uvmsc_boost::detail::is_function_impl<T>::value)
#ifndef UVMSC_BOOST_NO_RVALUE_REFERENCES
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_PARTIAL_SPEC1_1(typename T,is_function,T&&,false)
#endif
#endif
} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_FUNCTION_HPP_INCLUDED
