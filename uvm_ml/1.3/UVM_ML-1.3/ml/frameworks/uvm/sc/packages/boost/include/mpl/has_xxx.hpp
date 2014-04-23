
#ifndef UVMSC_BOOST_MPL_HAS_XXX_HPP_INCLUDED
#define UVMSC_BOOST_MPL_HAS_XXX_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2002-2006
// Copyright David Abrahams 2002-2003
// Copyright Daniel Walker 2007
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: has_xxx.hpp 64146 2010-07-19 00:46:31Z djwalker $
// $Date: 2010-07-18 20:46:31 -0400 (Sun, 18 Jul 2010) $
// $Revision: 64146 $

#include <packages/boost/include/mpl/bool.hpp>
#include <packages/boost/include/mpl/aux_/na_spec.hpp>
#include <packages/boost/include/mpl/aux_/type_wrapper.hpp>
#include <packages/boost/include/mpl/aux_/yes_no.hpp>
#include <packages/boost/include/mpl/aux_/config/gcc.hpp>
#include <packages/boost/include/mpl/aux_/config/has_xxx.hpp>
#include <packages/boost/include/mpl/aux_/config/msvc_typename.hpp>
#include <packages/boost/include/mpl/aux_/config/msvc.hpp>
#include <packages/boost/include/mpl/aux_/config/static_constant.hpp>
#include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#include <packages/boost/include/preprocessor/array/elem.hpp>
#include <packages/boost/include/preprocessor/cat.hpp>
#include <packages/boost/include/preprocessor/control/if.hpp>
#include <packages/boost/include/preprocessor/repetition/enum_params.hpp>
#include <packages/boost/include/preprocessor/repetition/enum_trailing_params.hpp>

#if UVMSC_BOOST_WORKAROUND( __BORLANDC__, UVMSC_BOOST_TESTED_AT(0x590) )
# include <packages/boost/include/type_traits/is_class.hpp>
#endif

#if !defined(UVMSC_BOOST_MPL_CFG_NO_HAS_XXX)

#   if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1300)

// agurt, 11/sep/02: MSVC-specific version (< 7.1), based on a USENET 
// newsgroup's posting by John Madsen (comp.lang.c++.moderated, 
// 1999-11-12 19:17:06 GMT); the code is _not_ standard-conforming, but 
// it works way more reliably than the SFINAE-based implementation

// Modified dwa 8/Oct/02 to handle reference types.

#   include <packages/boost/include/mpl/if.hpp>
#   include <packages/boost/include/mpl/bool.hpp>

namespace uvmsc_boost { namespace mpl { namespace aux {

struct has_xxx_tag;

#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, == 1300)
template< typename U > struct msvc_incomplete_array
{
    typedef char (&type)[sizeof(U) + 1];
};
#endif

template< typename T >
struct msvc_is_incomplete
{
    // MSVC is capable of some kinds of SFINAE.  If U is an incomplete
    // type, it won't pick the second overload
    static char tester(...);

#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, == 1300)
    template< typename U >
    static typename msvc_incomplete_array<U>::type tester(type_wrapper<U>);
#else
    template< typename U >
    static char (& tester(type_wrapper<U>) )[sizeof(U)+1];
#endif 
    
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = 
          sizeof(tester(type_wrapper<T>())) == 1
        );
};

template<>
struct msvc_is_incomplete<int>
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = false);
};

}}}

#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF_(trait, name, default_) \
template< typename T, typename name = ::uvmsc_boost::mpl::aux::has_xxx_tag > \
struct UVMSC_BOOST_PP_CAT(trait,_impl) : T \
{ \
    static uvmsc_boost::mpl::aux::no_tag \
    test(void(*)(::uvmsc_boost::mpl::aux::has_xxx_tag)); \
    \
    static uvmsc_boost::mpl::aux::yes_tag test(...); \
    \
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = \
          sizeof(test(static_cast<void(*)(name)>(0))) \
            != sizeof(uvmsc_boost::mpl::aux::no_tag) \
        ); \
    typedef uvmsc_boost::mpl::bool_<value> type; \
}; \
\
template< typename T, typename fallback_ = uvmsc_boost::mpl::bool_<default_> > \
struct trait \
    : uvmsc_boost::mpl::if_c< \
          uvmsc_boost::mpl::aux::msvc_is_incomplete<T>::value \
        , uvmsc_boost::mpl::bool_<false> \
        , UVMSC_BOOST_PP_CAT(trait,_impl)<T> \
        >::type \
{ \
}; \
\
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, void) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, bool) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, char) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, signed char) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, unsigned char) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, signed short) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, unsigned short) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, signed int) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, unsigned int) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, signed long) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, unsigned long) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, float) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, double) \
UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, long double) \
/**/

#   define UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, T) \
template<> struct trait<T> \
{ \
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = false); \
    typedef uvmsc_boost::mpl::bool_<false> type; \
}; \
/**/

#if !defined(UVMSC_BOOST_NO_INTRINSIC_WCHAR_T)
#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(trait, name, unused) \
    UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF_(trait, name, unused) \
    UVMSC_BOOST_MPL_AUX_HAS_XXX_TRAIT_SPEC(trait, wchar_t) \
/**/
#else
#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(trait, name, unused) \
    UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF_(trait, name, unused) \
/**/
#endif


// SFINAE-based implementations below are derived from a USENET newsgroup's 
// posting by Rani Sharoni (comp.lang.c++.moderated, 2002-03-17 07:45:09 PST)

#   elif UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, UVMSC_BOOST_TESTED_AT(1400)) \
      || UVMSC_BOOST_WORKAROUND(__IBMCPP__, <= 700)

// MSVC 7.1+ & VACPP

// agurt, 15/jun/05: replace overload-based SFINAE implementation with SFINAE
// applied to partial specialization to fix some apparently random failures 
// (thanks to Daniel Wallin for researching this!)

#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(trait, name, default_) \
template< typename T > \
struct UVMSC_BOOST_PP_CAT(trait, _msvc_sfinae_helper) \
{ \
    typedef void type; \
};\
\
template< typename T, typename U = void > \
struct UVMSC_BOOST_PP_CAT(trait,_impl_) \
{ \
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = false); \
    typedef uvmsc_boost::mpl::bool_<value> type; \
}; \
\
template< typename T > \
struct UVMSC_BOOST_PP_CAT(trait,_impl_)< \
      T \
    , typename UVMSC_BOOST_PP_CAT(trait, _msvc_sfinae_helper)< typename T::name >::type \
    > \
{ \
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = true); \
    typedef uvmsc_boost::mpl::bool_<value> type; \
}; \
\
template< typename T, typename fallback_ = uvmsc_boost::mpl::bool_<default_> > \
struct trait \
    : UVMSC_BOOST_PP_CAT(trait,_impl_)<T> \
{ \
}; \
/**/

#   elif UVMSC_BOOST_WORKAROUND( __BORLANDC__, UVMSC_BOOST_TESTED_AT(0x590) )

#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_BCB_DEF(trait, trait_tester, name, default_) \
template< typename T, bool IS_CLASS > \
struct trait_tester \
{ \
    UVMSC_BOOST_STATIC_CONSTANT( bool,  value = false ); \
}; \
template< typename T > \
struct trait_tester< T, true > \
{ \
    struct trait_tester_impl \
    { \
        template < class U > \
        static int  resolve( uvmsc_boost::mpl::aux::type_wrapper<U> const volatile * \
                           , uvmsc_boost::mpl::aux::type_wrapper<typename U::name >* = 0 ); \
        static char resolve( ... ); \
    }; \
    typedef uvmsc_boost::mpl::aux::type_wrapper<T> t_; \
    UVMSC_BOOST_STATIC_CONSTANT( bool, value = ( sizeof( trait_tester_impl::resolve( static_cast< t_ * >(0) ) ) == sizeof(int) ) ); \
}; \
template< typename T, typename fallback_ = uvmsc_boost::mpl::bool_<default_> > \
struct trait           \
{                      \
    UVMSC_BOOST_STATIC_CONSTANT( bool, value = (trait_tester< T, uvmsc_boost::is_class< T >::value >::value) );     \
    typedef uvmsc_boost::mpl::bool_< trait< T, fallback_ >::value > type; \
};

#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(trait, name, default_) \
    UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_BCB_DEF( trait \
                                         , UVMSC_BOOST_PP_CAT(trait,_tester)      \
                                         , name       \
                                         , default_ ) \
/**/

#   else // other SFINAE-capable compilers

#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(trait, name, default_) \
template< typename T, typename fallback_ = uvmsc_boost::mpl::bool_<default_> > \
struct trait \
{ \
    struct gcc_3_2_wknd \
    { \
        template< typename U > \
        static uvmsc_boost::mpl::aux::yes_tag test( \
              uvmsc_boost::mpl::aux::type_wrapper<U> const volatile* \
            , uvmsc_boost::mpl::aux::type_wrapper<UVMSC_BOOST_MSVC_TYPENAME U::name>* = 0 \
            ); \
    \
        static uvmsc_boost::mpl::aux::no_tag test(...); \
    }; \
    \
    typedef uvmsc_boost::mpl::aux::type_wrapper<T> t_; \
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = \
          sizeof(gcc_3_2_wknd::test(static_cast<t_*>(0))) \
            == sizeof(uvmsc_boost::mpl::aux::yes_tag) \
        ); \
    typedef uvmsc_boost::mpl::bool_<value> type; \
}; \
/**/

#   endif // UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1300)


#else // UVMSC_BOOST_MPL_CFG_NO_HAS_XXX

// placeholder implementation

#   define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(trait, name, default_) \
template< typename T, typename fallback_ = uvmsc_boost::mpl::bool_<default_> > \
struct trait \
{ \
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = fallback_::value); \
    typedef fallback_ type; \
}; \
/**/

#endif

#define UVMSC_BOOST_MPL_HAS_XXX_TRAIT_DEF(name) \
    UVMSC_BOOST_MPL_HAS_XXX_TRAIT_NAMED_DEF(UVMSC_BOOST_PP_CAT(has_,name), name, false) \
/**/


#if !defined(UVMSC_BOOST_MPL_CFG_NO_HAS_XXX_TEMPLATE)

// Create a boolean Metafunction to detect a nested template
// member. This implementation is based on a USENET newsgroup's
// posting by Aleksey Gurtovoy (comp.lang.c++.moderated, 2002-03-19),
// Rani Sharoni's USENET posting cited above, the non-template has_xxx
// implementations above, and discussion on the Boost mailing list.

#   if !defined(UVMSC_BOOST_MPL_HAS_XXX_NO_WRAPPED_TYPES)
#     if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1400)
#       define UVMSC_BOOST_MPL_HAS_XXX_NO_WRAPPED_TYPES 1
#     endif
#   endif

#   if !defined(UVMSC_BOOST_MPL_HAS_XXX_NO_EXPLICIT_TEST_FUNCTION)
#     if (defined(UVMSC_BOOST_NO_EXPLICIT_FUNCTION_TEMPLATE_ARGUMENTS))
#       define UVMSC_BOOST_MPL_HAS_XXX_NO_EXPLICIT_TEST_FUNCTION 1
#     endif
#   endif

#   if !defined(UVMSC_BOOST_MPL_HAS_XXX_NEEDS_TEMPLATE_SFINAE)
#     if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1400)
#       define UVMSC_BOOST_MPL_HAS_XXX_NEEDS_TEMPLATE_SFINAE 1
#     endif
#   endif

// NOTE: Many internal implementation macros take a Boost.Preprocessor
// array argument called args which is of the following form.
//           ( 4, ( trait, name, max_arity, default_ ) )

#   define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_NAME(args) \
      UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_ARRAY_ELEM(0, args) , _introspect) \
    /**/

#   define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME(args, n) \
      UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_ARRAY_ELEM(0, args) , _substitute), n) \
    /**/

#   define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args) \
      UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_ARRAY_ELEM(0, args) , _test) \
    /**/

// Thanks to Guillaume Melquiond for pointing out the need for the
// "substitute" template as an argument to the overloaded test
// functions to get SFINAE to work for member templates with the
// correct name but different number of arguments.
#   define UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_SUBSTITUTE(z, n, args) \
      template< \
          template< UVMSC_BOOST_PP_ENUM_PARAMS(UVMSC_BOOST_PP_INC(n), typename V) > class V \
       > \
      struct UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME(args, n) { \
      }; \
    /**/

#   define UVMSC_BOOST_MPL_HAS_MEMBER_SUBSTITUTE(args, substitute_macro) \
      UVMSC_BOOST_PP_REPEAT( \
          UVMSC_BOOST_PP_ARRAY_ELEM(2, args) \
        , UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_SUBSTITUTE \
        , args \
      ) \
    /**/

#   if !UVMSC_BOOST_MPL_HAS_XXX_NO_EXPLICIT_TEST_FUNCTION
#     define UVMSC_BOOST_MPL_HAS_MEMBER_REJECT(args, member_macro) \
        template< typename V > \
        static uvmsc_boost::mpl::aux::no_tag \
        UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)(...); \
      /**/
#   else
#     define UVMSC_BOOST_MPL_HAS_MEMBER_REJECT(args, member_macro) \
        static uvmsc_boost::mpl::aux::no_tag \
        UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)(...); \
      /**/
#   endif

#   if !UVMSC_BOOST_MPL_HAS_XXX_NO_WRAPPED_TYPES
#     define UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_ACCEPT(z, n, args) \
        template< typename V > \
        static uvmsc_boost::mpl::aux::yes_tag \
        UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)( \
            uvmsc_boost::mpl::aux::type_wrapper< V > const volatile* \
          , UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME(args, n) < \
                V::template UVMSC_BOOST_PP_ARRAY_ELEM(1, args) \
            >* = 0 \
        ); \
      /**/
#     define UVMSC_BOOST_MPL_HAS_MEMBER_ACCEPT(args, member_macro) \
        UVMSC_BOOST_PP_REPEAT( \
            UVMSC_BOOST_PP_ARRAY_ELEM(2, args) \
          , UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_ACCEPT \
          , args \
        ) \
      /**/
#   else
#     define UVMSC_BOOST_MPL_HAS_MEMBER_ACCEPT(args, member_macro) \
        template< typename V > \
        static uvmsc_boost::mpl::aux::yes_tag \
        UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)( \
            V const volatile* \
          , member_macro(args, V, T)* = 0 \
        ); \
      /**/
#   endif

#   if !UVMSC_BOOST_MPL_HAS_XXX_NO_EXPLICIT_TEST_FUNCTION
#     define UVMSC_BOOST_MPL_HAS_MEMBER_TEST(args) \
          sizeof(UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)< U >(0)) \
              == sizeof(uvmsc_boost::mpl::aux::yes_tag) \
      /**/
#   else
#     if !UVMSC_BOOST_MPL_HAS_XXX_NO_WRAPPED_TYPES
#       define UVMSC_BOOST_MPL_HAS_MEMBER_TEST(args) \
          sizeof( \
              UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)( \
                  static_cast< uvmsc_boost::mpl::aux::type_wrapper< U >* >(0) \
              ) \
          ) == sizeof(uvmsc_boost::mpl::aux::yes_tag) \
        /**/
#     else
#       define UVMSC_BOOST_MPL_HAS_MEMBER_TEST(args) \
          sizeof( \
              UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)( \
                  static_cast< U* >(0) \
              ) \
          ) == sizeof(uvmsc_boost::mpl::aux::yes_tag) \
        /**/
#     endif
#   endif

#   define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECT( \
               args, substitute_macro, member_macro \
           ) \
      template< typename U > \
      struct UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_NAME(args) { \
          UVMSC_BOOST_MPL_HAS_MEMBER_SUBSTITUTE(args, substitute_macro) \
          UVMSC_BOOST_MPL_HAS_MEMBER_REJECT(args, member_macro) \
          UVMSC_BOOST_MPL_HAS_MEMBER_ACCEPT(args, member_macro) \
          UVMSC_BOOST_STATIC_CONSTANT( \
              bool, value = UVMSC_BOOST_MPL_HAS_MEMBER_TEST(args) \
          ); \
          typedef uvmsc_boost::mpl::bool_< value > type; \
      }; \
    /**/

#   define UVMSC_BOOST_MPL_HAS_MEMBER_IMPLEMENTATION( \
               args, introspect_macro, substitute_macro, member_macro \
           ) \
      template< \
          typename T \
        , typename fallback_ \
              = uvmsc_boost::mpl::bool_< UVMSC_BOOST_PP_ARRAY_ELEM(3, args) > \
      > \
      class UVMSC_BOOST_PP_ARRAY_ELEM(0, args) { \
          introspect_macro(args, substitute_macro, member_macro) \
      public: \
          static const bool value \
              = UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_NAME(args)< T >::value; \
          typedef typename UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_NAME(args)< \
              T \
          >::type type; \
      }; \
    /**/

// UVMSC_BOOST_MPL_HAS_MEMBER_WITH_FUNCTION_SFINAE expands to the full
// implementation of the function-based metafunction. Compile with -E
// to see the preprocessor output for this macro.
#   define UVMSC_BOOST_MPL_HAS_MEMBER_WITH_FUNCTION_SFINAE( \
               args, substitute_macro, member_macro \
           ) \
      UVMSC_BOOST_MPL_HAS_MEMBER_IMPLEMENTATION( \
          args \
        , UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECT \
        , substitute_macro \
        , member_macro \
      ) \
    /**/

#   if UVMSC_BOOST_MPL_HAS_XXX_NEEDS_TEMPLATE_SFINAE

#     if !defined(UVMSC_BOOST_MPL_HAS_XXX_NEEDS_NAMESPACE_LEVEL_SUBSTITUTE)
#       if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1400)
#         define UVMSC_BOOST_MPL_HAS_XXX_NEEDS_NAMESPACE_LEVEL_SUBSTITUTE 1
#       endif
#     endif

#     if !UVMSC_BOOST_MPL_HAS_XXX_NEEDS_NAMESPACE_LEVEL_SUBSTITUTE
#       define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME_WITH_TEMPLATE_SFINAE( \
                   args, n \
               ) \
          UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME(args, n) \
        /**/
#     else
#       define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME_WITH_TEMPLATE_SFINAE( \
                   args, n \
               ) \
          UVMSC_BOOST_PP_CAT( \
              boost_mpl_has_xxx_ \
            , UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME(args, n) \
          ) \
        /**/
#     endif

#     define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_TAG_NAME( \
                 args \
             ) \
        UVMSC_BOOST_PP_CAT( \
            UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME_WITH_TEMPLATE_SFINAE( \
                args, 0 \
            ) \
          , _tag \
        ) \
      /**/

#     define UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_SUBSTITUTE_WITH_TEMPLATE_SFINAE( \
                 z, n, args \
             ) \
        template< \
             template< UVMSC_BOOST_PP_ENUM_PARAMS(UVMSC_BOOST_PP_INC(n), typename U) > class U \
        > \
        struct UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME_WITH_TEMPLATE_SFINAE( \
                args, n \
               ) { \
            typedef \
                UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_TAG_NAME(args) \
                type; \
        }; \
      /**/

#     define UVMSC_BOOST_MPL_HAS_MEMBER_SUBSTITUTE_WITH_TEMPLATE_SFINAE( \
                 args, substitute_macro \
             ) \
        typedef void \
            UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_TAG_NAME(args); \
        UVMSC_BOOST_PP_REPEAT( \
            UVMSC_BOOST_PP_ARRAY_ELEM(2, args) \
          , UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_SUBSTITUTE_WITH_TEMPLATE_SFINAE \
          , args \
        ) \
      /**/

#     define UVMSC_BOOST_MPL_HAS_MEMBER_REJECT_WITH_TEMPLATE_SFINAE( \
                 args, member_macro \
             ) \
        template< \
            typename U \
          , typename V \
                = UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_TAG_NAME(args) \
        > \
        struct UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args) { \
            UVMSC_BOOST_STATIC_CONSTANT(bool, value = false); \
            typedef uvmsc_boost::mpl::bool_< value > type; \
        }; \
      /**/

#     define UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_ACCEPT_WITH_TEMPLATE_SFINAE( \
                 z, n, args \
             ) \
        template< typename U > \
        struct UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)< \
            U \
          , typename \
                UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_SUBSTITUTE_NAME_WITH_TEMPLATE_SFINAE( \
                    args, n \
                )< \
                    UVMSC_BOOST_MSVC_TYPENAME U::UVMSC_BOOST_PP_ARRAY_ELEM(1, args)< > \
                >::type \
        > { \
            UVMSC_BOOST_STATIC_CONSTANT(bool, value = true); \
            typedef uvmsc_boost::mpl::bool_< value > type; \
        }; \
      /**/

#     define UVMSC_BOOST_MPL_HAS_MEMBER_ACCEPT_WITH_TEMPLATE_SFINAE( \
                 args, member_macro \
             ) \
        UVMSC_BOOST_PP_REPEAT( \
            UVMSC_BOOST_PP_ARRAY_ELEM(2, args) \
          , UVMSC_BOOST_MPL_HAS_MEMBER_MULTI_ACCEPT_WITH_TEMPLATE_SFINAE \
          , args \
        ) \
      /**/

#     define UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECT_WITH_TEMPLATE_SFINAE( \
                 args, substitute_macro, member_macro \
             ) \
        UVMSC_BOOST_MPL_HAS_MEMBER_REJECT_WITH_TEMPLATE_SFINAE(args, member_macro) \
        UVMSC_BOOST_MPL_HAS_MEMBER_ACCEPT_WITH_TEMPLATE_SFINAE(args, member_macro) \
        template< typename U > \
        struct UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_NAME(args) \
            : UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECTION_TEST_NAME(args)< U > { \
        }; \
      /**/
 
// UVMSC_BOOST_MPL_HAS_MEMBER_WITH_TEMPLATE_SFINAE expands to the full
// implementation of the template-based metafunction. Compile with -E
// to see the preprocessor output for this macro.
//
// Note that if UVMSC_BOOST_MPL_HAS_XXX_NEEDS_NAMESPACE_LEVEL_SUBSTITUTE is
// defined UVMSC_BOOST_MPL_HAS_MEMBER_SUBSTITUTE_WITH_TEMPLATE_SFINAE needs
// to be expanded at namespace level before
// UVMSC_BOOST_MPL_HAS_MEMBER_WITH_TEMPLATE_SFINAE can be used.
#     define UVMSC_BOOST_MPL_HAS_MEMBER_WITH_TEMPLATE_SFINAE( \
                 args, substitute_macro, member_macro \
             ) \
        UVMSC_BOOST_MPL_HAS_MEMBER_SUBSTITUTE_WITH_TEMPLATE_SFINAE( \
            args, substitute_macro \
        ) \
        UVMSC_BOOST_MPL_HAS_MEMBER_IMPLEMENTATION( \
            args \
          , UVMSC_BOOST_MPL_HAS_MEMBER_INTROSPECT_WITH_TEMPLATE_SFINAE \
          , substitute_macro \
          , member_macro \
        ) \
      /**/

#   endif // UVMSC_BOOST_MPL_HAS_XXX_NEEDS_TEMPLATE_SFINAE

// Note: In the current implementation the parameter and access macros
// are no longer expanded.
#   if !UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1400)
#     define UVMSC_BOOST_MPL_HAS_XXX_TEMPLATE_NAMED_DEF(trait, name, default_) \
        UVMSC_BOOST_MPL_HAS_MEMBER_WITH_FUNCTION_SFINAE( \
            ( 4, ( trait, name, UVMSC_BOOST_MPL_LIMIT_METAFUNCTION_ARITY, default_ ) ) \
          , UVMSC_BOOST_MPL_HAS_MEMBER_TEMPLATE_SUBSTITUTE_PARAMETER \
          , UVMSC_BOOST_MPL_HAS_MEMBER_TEMPLATE_ACCESS \
        ) \
      /**/
#   else
#     define UVMSC_BOOST_MPL_HAS_XXX_TEMPLATE_NAMED_DEF(trait, name, default_) \
        UVMSC_BOOST_MPL_HAS_MEMBER_WITH_TEMPLATE_SFINAE( \
            ( 4, ( trait, name, UVMSC_BOOST_MPL_LIMIT_METAFUNCTION_ARITY, default_ ) ) \
          , UVMSC_BOOST_MPL_HAS_MEMBER_TEMPLATE_SUBSTITUTE_PARAMETER \
          , UVMSC_BOOST_MPL_HAS_MEMBER_TEMPLATE_ACCESS \
        ) \
      /**/
#   endif

#else // UVMSC_BOOST_MPL_CFG_NO_HAS_XXX_TEMPLATE

// placeholder implementation

#   define UVMSC_BOOST_MPL_HAS_XXX_TEMPLATE_NAMED_DEF(trait, name, default_) \
      template< typename T \
              , typename fallback_ = uvmsc_boost::mpl::bool_< default_ > > \
      struct trait { \
          UVMSC_BOOST_STATIC_CONSTANT(bool, value = fallback_::value); \
          typedef fallback_ type; \
      }; \
    /**/

#endif // UVMSC_BOOST_MPL_CFG_NO_HAS_XXX_TEMPLATE

#   define UVMSC_BOOST_MPL_HAS_XXX_TEMPLATE_DEF(name) \
      UVMSC_BOOST_MPL_HAS_XXX_TEMPLATE_NAMED_DEF( \
          UVMSC_BOOST_PP_CAT(has_, name), name, false \
      ) \
    /**/

#endif // UVMSC_BOOST_MPL_HAS_XXX_HPP_INCLUDED
