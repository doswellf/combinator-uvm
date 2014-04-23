
//  (C) Copyright Dave Abrahams, Steve Cleary, Beman Dawes, Howard
//  Hinnant & John Maddock 2000.  
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.


#ifndef UVMSC_BOOST_TT_DETAIL_CV_TRAITS_IMPL_HPP_INCLUDED
#define UVMSC_BOOST_TT_DETAIL_CV_TRAITS_IMPL_HPP_INCLUDED

#include <packages/boost/include/config.hpp>
#include <packages/boost/include/detail/workaround.hpp>

#ifndef UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

// implementation helper:


#if !(UVMSC_BOOST_WORKAROUND(__GNUC__,== 3) && UVMSC_BOOST_WORKAROUND(__GNUC_MINOR__, <= 2))
namespace uvmsc_boost {
namespace detail {
#else
#include <packages/boost/include/type_traits/detail/yes_no_type.hpp>
namespace uvmsc_boost {
namespace type_traits {
namespace gcc8503 {
#endif

template <typename T> struct cv_traits_imp {};

template <typename T>
struct cv_traits_imp<T*>
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_const = false);
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_volatile = false);
    typedef T unqualified_type;
};

template <typename T>
struct cv_traits_imp<const T*>
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_const = true);
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_volatile = false);
    typedef T unqualified_type;
};

template <typename T>
struct cv_traits_imp<volatile T*>
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_const = false);
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_volatile = true);
    typedef T unqualified_type;
};

template <typename T>
struct cv_traits_imp<const volatile T*>
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_const = true);
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_volatile = true);
    typedef T unqualified_type;
};

#if UVMSC_BOOST_WORKAROUND(__GNUC__,== 3) && UVMSC_BOOST_WORKAROUND(__GNUC_MINOR__, <= 2)
// We have to exclude function pointers 
// (see http://gcc.gnu.org/bugzilla/show_bug.cgi?8503)
yes_type mini_funcptr_tester(...);
no_type  mini_funcptr_tester(const volatile void*);

} // namespace gcc8503
} // namespace type_traits

namespace detail {

// Use the implementation above for non function pointers
template <typename T, unsigned Select 
  = (unsigned)sizeof(::uvmsc_boost::type_traits::gcc8503::mini_funcptr_tester((T)0)) >
struct cv_traits_imp : public ::uvmsc_boost::type_traits::gcc8503::cv_traits_imp<T> { };

// Functions are never cv-qualified
template <typename T> struct cv_traits_imp<T*,1>
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_const = false);
    UVMSC_BOOST_STATIC_CONSTANT(bool, is_volatile = false);
    typedef T unqualified_type;
};

#endif

} // namespace detail
} // namespace uvmsc_boost 

#endif // UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

#endif // UVMSC_BOOST_TT_DETAIL_CV_TRAITS_IMPL_HPP_INCLUDED
