//  (C) Copyright Dave Abrahams, Steve Cleary, Beman Dawes, Howard
//  Hinnant & John Maddock 2000-2003.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.


#ifndef UVMSC_BOOST_TT_IS_CLASS_HPP_INCLUDED
#define UVMSC_BOOST_TT_IS_CLASS_HPP_INCLUDED

#include <packages/boost/include/type_traits/config.hpp>
#include <packages/boost/include/type_traits/intrinsics.hpp>
#ifndef UVMSC_BOOST_IS_CLASS
#   include <packages/boost/include/type_traits/is_union.hpp>
#   include <packages/boost/include/type_traits/detail/ice_and.hpp>
#   include <packages/boost/include/type_traits/detail/ice_not.hpp>

#ifdef UVMSC_BOOST_TT_HAS_CONFORMING_IS_CLASS_IMPLEMENTATION
#   include <packages/boost/include/type_traits/detail/yes_no_type.hpp>
#else
#   include <packages/boost/include/type_traits/is_scalar.hpp>
#   include <packages/boost/include/type_traits/is_array.hpp>
#   include <packages/boost/include/type_traits/is_reference.hpp>
#   include <packages/boost/include/type_traits/is_void.hpp>
#   include <packages/boost/include/type_traits/is_function.hpp>
#endif

#endif // UVMSC_BOOST_IS_CLASS

#ifdef __EDG_VERSION__
#   include <packages/boost/include/type_traits/remove_cv.hpp>
#endif

// should be the last #include
#include <packages/boost/include/type_traits/detail/bool_trait_def.hpp>

namespace uvmsc_boost {

namespace detail {

#ifndef UVMSC_BOOST_IS_CLASS
#ifdef UVMSC_BOOST_TT_HAS_CONFORMING_IS_CLASS_IMPLEMENTATION

// This is actually the conforming implementation which works with
// abstract classes.  However, enough compilers have trouble with
// it that most will use the one in
// packages/boost/include/type_traits/object_traits.hpp. This implementation
// actually works with VC7.0, but other interactions seem to fail
// when we use it.

// is_class<> metafunction due to Paul Mensonides
// (leavings@attbi.com). For more details:
// http://groups.google.com/groups?hl=en&selm=000001c1cc83%24e154d5e0%247772e50c%40c161550a&rnum=1
#if defined(__GNUC__)  && !defined(__EDG_VERSION__)

template <class U> ::uvmsc_boost::type_traits::yes_type is_class_tester(void(U::*)(void));
template <class U> ::uvmsc_boost::type_traits::no_type is_class_tester(...);

template <typename T>
struct is_class_impl
{

    UVMSC_BOOST_STATIC_CONSTANT(bool, value =
        (::uvmsc_boost::type_traits::ice_and<
            sizeof(is_class_tester<T>(0)) == sizeof(::uvmsc_boost::type_traits::yes_type),
            ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_union<T>::value >::value
        >::value)
        );
};

#else

template <typename T>
struct is_class_impl
{
    template <class U> static ::uvmsc_boost::type_traits::yes_type is_class_tester(void(U::*)(void));
    template <class U> static ::uvmsc_boost::type_traits::no_type is_class_tester(...);

    UVMSC_BOOST_STATIC_CONSTANT(bool, value =
        (::uvmsc_boost::type_traits::ice_and<
            sizeof(is_class_tester<T>(0)) == sizeof(::uvmsc_boost::type_traits::yes_type),
            ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_union<T>::value >::value
        >::value)
        );
};

#endif

#else

template <typename T>
struct is_class_impl
{
#   ifndef UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION
    UVMSC_BOOST_STATIC_CONSTANT(bool, value =
    (::uvmsc_boost::type_traits::ice_and<
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_union<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_scalar<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_array<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_reference<T>::value>::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_void<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_function<T>::value >::value
        >::value));
#   else
    UVMSC_BOOST_STATIC_CONSTANT(bool, value =
    (::uvmsc_boost::type_traits::ice_and<
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_union<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_scalar<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_array<T>::value >::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_reference<T>::value>::value,
        ::uvmsc_boost::type_traits::ice_not< ::uvmsc_boost::is_void<T>::value >::value
        >::value));
#   endif
};

# endif // UVMSC_BOOST_TT_HAS_CONFORMING_IS_CLASS_IMPLEMENTATION
# else // UVMSC_BOOST_IS_CLASS
template <typename T>
struct is_class_impl
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = UVMSC_BOOST_IS_CLASS(T));
};
# endif // UVMSC_BOOST_IS_CLASS

} // namespace detail

# ifdef __EDG_VERSION__
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(
   is_class,T, uvmsc_boost::detail::is_class_impl<typename uvmsc_boost::remove_cv<T>::type>::value)
# else 
UVMSC_BOOST_TT_AUX_BOOL_TRAIT_DEF1(is_class,T,::uvmsc_boost::detail::is_class_impl<T>::value)
# endif
    
} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/bool_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_IS_CLASS_HPP_INCLUDED
