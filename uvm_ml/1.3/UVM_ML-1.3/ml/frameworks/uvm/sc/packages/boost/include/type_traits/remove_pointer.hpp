
//  (C) Copyright Steve Cleary, Beman Dawes, Howard Hinnant & John Maddock 2000.
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.

#ifndef UVMSC_BOOST_TT_REMOVE_POINTER_HPP_INCLUDED
#define UVMSC_BOOST_TT_REMOVE_POINTER_HPP_INCLUDED

#include <packages/boost/include/config.hpp>
#include <packages/boost/include/detail/workaround.hpp>
#ifdef UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION
#include <packages/boost/include/type_traits/broken_compiler_spec.hpp>
#endif

#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC,<=1300)
#include <packages/boost/include/type_traits/msvc/remove_pointer.hpp>
#elif defined(UVMSC_BOOST_MSVC)
#include <packages/boost/include/type_traits/remove_cv.hpp>
#include <packages/boost/include/type_traits/is_pointer.hpp>
#endif

// should be the last #include
#include <packages/boost/include/type_traits/detail/type_trait_def.hpp>

namespace uvmsc_boost {

#ifdef UVMSC_BOOST_MSVC

namespace detail{

   //
   // We need all this crazy indirection because a type such as:
   //
   // T (*const)(U)
   //
   // Does not bind to a <T*> or <T*const> partial specialization with VC10 and earlier
   //
   template <class T> 
   struct remove_pointer_imp
   {
      typedef T type;
   };

   template <class T> 
   struct remove_pointer_imp<T*>
   {
      typedef T type;
   };

   template <class T, bool b> 
   struct remove_pointer_imp3
   {
      typedef typename remove_pointer_imp<typename uvmsc_boost::remove_cv<T>::type>::type type;
   };

   template <class T> 
   struct remove_pointer_imp3<T, false>
   {
      typedef T type;
   };

   template <class T> 
   struct remove_pointer_imp2
   {
      typedef typename remove_pointer_imp3<T, ::uvmsc_boost::is_pointer<T>::value>::type type;
   };
}

UVMSC_BOOST_TT_AUX_TYPE_TRAIT_DEF1(remove_pointer,T,typename uvmsc_boost::detail::remove_pointer_imp2<T>::type)

#elif !defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION)

UVMSC_BOOST_TT_AUX_TYPE_TRAIT_DEF1(remove_pointer,T,T)
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_1(typename T,remove_pointer,T*,T)
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_1(typename T,remove_pointer,T* const,T)
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_1(typename T,remove_pointer,T* volatile,T)
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_1(typename T,remove_pointer,T* const volatile,T)

#elif !UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC,<=1300)

UVMSC_BOOST_TT_AUX_TYPE_TRAIT_DEF1(remove_pointer,T,typename uvmsc_boost::detail::remove_pointer_impl<T>::type)

#endif

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/type_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_REMOVE_POINTER_HPP_INCLUDED
