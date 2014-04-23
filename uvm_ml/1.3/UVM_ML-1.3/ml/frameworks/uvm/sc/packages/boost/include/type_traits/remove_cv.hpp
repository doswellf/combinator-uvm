
//  (C) Copyright Dave Abrahams, Steve Cleary, Beman Dawes, Howard
//  Hinnant & John Maddock 2000.  
//  Use, modification and distribution are subject to the Boost Software License,
//  Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt).
//
//  See http://www.boost.org/libs/type_traits for most recent version including documentation.


#ifndef UVMSC_BOOST_TT_REMOVE_CV_HPP_INCLUDED
#define UVMSC_BOOST_TT_REMOVE_CV_HPP_INCLUDED

#include <packages/boost/include/type_traits/broken_compiler_spec.hpp>
#include <packages/boost/include/type_traits/detail/cv_traits_impl.hpp>
#include <packages/boost/include/config.hpp>
#include <packages/boost/include/detail/workaround.hpp>

#include <cstddef>

#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC,<=1300)
#include <packages/boost/include/type_traits/msvc/remove_cv.hpp>
#endif

// should be the last #include
#include <packages/boost/include/type_traits/detail/type_trait_def.hpp>

namespace uvmsc_boost {

#ifndef UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

namespace detail{

template <class T>
struct rvalue_ref_filter_rem_cv
{
   typedef typename uvmsc_boost::detail::cv_traits_imp<T*>::unqualified_type type;
};

#ifndef UVMSC_BOOST_NO_RVALUE_REFERENCES
//
// We can't filter out rvalue_references at the same level as
// references or we get ambiguities from msvc:
//
template <class T>
struct rvalue_ref_filter_rem_cv<T&&>
{
   typedef T&& type;
};
#endif

}


//  convert a type T to a non-cv-qualified type - remove_cv<T>
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_DEF1(remove_cv,T,typename uvmsc_boost::detail::rvalue_ref_filter_rem_cv<T>::type)
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_1(typename T,remove_cv,T&,T&)
#if !defined(UVMSC_BOOST_NO_ARRAY_TYPE_SPECIALIZATIONS)
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,remove_cv,T const[N],T type[N])
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,remove_cv,T volatile[N],T type[N])
UVMSC_BOOST_TT_AUX_TYPE_TRAIT_PARTIAL_SPEC1_2(typename T,std::size_t N,remove_cv,T const volatile[N],T type[N])
#endif

#elif !UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC,<=1300)

namespace detail {
template <typename T>
struct remove_cv_impl
{
    typedef typename remove_volatile_impl< 
          typename remove_const_impl<T>::type
        >::type type;
};
}

UVMSC_BOOST_TT_AUX_TYPE_TRAIT_DEF1(remove_cv,T,typename uvmsc_boost::detail::remove_cv_impl<T>::type)

#endif // UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION

} // namespace uvmsc_boost

#include <packages/boost/include/type_traits/detail/type_trait_undef.hpp>

#endif // UVMSC_BOOST_TT_REMOVE_CV_HPP_INCLUDED
