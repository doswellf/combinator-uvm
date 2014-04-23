
#ifndef UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2001-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: lambda_support.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/lambda.hpp>

#if !defined(UVMSC_BOOST_MPL_CFG_NO_FULL_LAMBDA_SUPPORT)

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) /**/
#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(i,name,params) /**/

#else

#   include <packages/boost/include/mpl/int_fwd.hpp>
#   include <packages/boost/include/mpl/aux_/yes_no.hpp>
#   include <packages/boost/include/mpl/aux_/na_fwd.hpp>
#   include <packages/boost/include/mpl/aux_/preprocessor/params.hpp>
#   include <packages/boost/include/mpl/aux_/preprocessor/enum.hpp>
#   include <packages/boost/include/mpl/aux_/config/msvc.hpp>
#   include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#   include <packages/boost/include/preprocessor/tuple/to_list.hpp>
#   include <packages/boost/include/preprocessor/list/for_each_i.hpp>
#   include <packages/boost/include/preprocessor/inc.hpp>
#   include <packages/boost/include/preprocessor/cat.hpp>

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_ARG_TYPEDEF_FUNC(R,typedef_,i,param) \
    typedef_ param UVMSC_BOOST_PP_CAT(arg,UVMSC_BOOST_PP_INC(i)); \
    /**/

// agurt, 07/mar/03: restore an old revision for the sake of SGI MIPSpro C++
#if UVMSC_BOOST_WORKAROUND(__EDG_VERSION__, <= 238) 

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(i, name, params) \
    typedef UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE::int_<i> arity; \
    UVMSC_BOOST_PP_LIST_FOR_EACH_I_R( \
          1 \
        , UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_ARG_TYPEDEF_FUNC \
        , typedef \
        , UVMSC_BOOST_PP_TUPLE_TO_LIST(i,params) \
        ) \
    struct rebind \
    { \
        template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename U) > struct apply \
            : name< UVMSC_BOOST_MPL_PP_PARAMS(i,U) > \
        { \
        }; \
    }; \
    /**/

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) \
    UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(i, name, params) \
    /**/

#elif UVMSC_BOOST_WORKAROUND(__EDG_VERSION__, <= 244) && !defined(UVMSC_BOOST_INTEL_CXX_VERSION)
// agurt, 18/jan/03: old EDG-based compilers actually enforce 11.4 para 9
// (in strict mode), so we have to provide an alternative to the 
// MSVC-optimized implementation

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) \
    typedef UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE::int_<i> arity; \
    UVMSC_BOOST_PP_LIST_FOR_EACH_I_R( \
          1 \
        , UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_ARG_TYPEDEF_FUNC \
        , typedef \
        , UVMSC_BOOST_PP_TUPLE_TO_LIST(i,params) \
        ) \
    struct rebind; \
/**/

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(i, name, params) \
    UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) \
}; \
template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename T) > \
struct name<UVMSC_BOOST_MPL_PP_PARAMS(i,T)>::rebind \
{ \
    template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename U) > struct apply \
        : name< UVMSC_BOOST_MPL_PP_PARAMS(i,U) > \
    { \
    }; \
/**/

#else // __EDG_VERSION__

namespace uvmsc_boost { namespace mpl { namespace aux {
template< typename T > struct has_rebind_tag;
}}}

#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) \
    typedef UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE::int_<i> arity; \
    UVMSC_BOOST_PP_LIST_FOR_EACH_I_R( \
          1 \
        , UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_ARG_TYPEDEF_FUNC \
        , typedef \
        , UVMSC_BOOST_PP_TUPLE_TO_LIST(i,params) \
        ) \
    friend class UVMSC_BOOST_PP_CAT(name,_rebind); \
    typedef UVMSC_BOOST_PP_CAT(name,_rebind) rebind; \
/**/

#if UVMSC_BOOST_WORKAROUND(__BORLANDC__, UVMSC_BOOST_TESTED_AT(0x610))
#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HAS_REBIND(i, name, params) \
template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename T) > \
::uvmsc_boost::mpl::aux::yes_tag operator|( \
      ::uvmsc_boost::mpl::aux::has_rebind_tag<int> \
    , name<UVMSC_BOOST_MPL_PP_PARAMS(i,T)>* \
    ); \
::uvmsc_boost::mpl::aux::no_tag operator|( \
      ::uvmsc_boost::mpl::aux::has_rebind_tag<int> \
    , name< UVMSC_BOOST_MPL_PP_ENUM(i,::uvmsc_boost::mpl::na) >* \
    ); \
/**/
#elif !UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, < 1300)
#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HAS_REBIND(i, name, params) \
template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename T) > \
::uvmsc_boost::mpl::aux::yes_tag operator|( \
      ::uvmsc_boost::mpl::aux::has_rebind_tag<int> \
    , ::uvmsc_boost::mpl::aux::has_rebind_tag< name<UVMSC_BOOST_MPL_PP_PARAMS(i,T)> >* \
    ); \
/**/
#else
#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HAS_REBIND(i, name, params) /**/
#endif

#   if !defined(__BORLANDC__)
#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(i, name, params) \
    UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) \
}; \
UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HAS_REBIND(i, name, params) \
class UVMSC_BOOST_PP_CAT(name,_rebind) \
{ \
 public: \
    template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename U) > struct apply \
        : name< UVMSC_BOOST_MPL_PP_PARAMS(i,U) > \
    { \
    }; \
/**/
#   else
#   define UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(i, name, params) \
    UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_SPEC(i, name, params) \
}; \
UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HAS_REBIND(i, name, params) \
class UVMSC_BOOST_PP_CAT(name,_rebind) \
{ \
 public: \
    template< UVMSC_BOOST_MPL_PP_PARAMS(i,typename U) > struct apply \
    { \
        typedef typename name< UVMSC_BOOST_MPL_PP_PARAMS(i,U) >::type type; \
    }; \
/**/
#   endif // __BORLANDC__

#endif // __EDG_VERSION__

#endif // UVMSC_BOOST_MPL_CFG_NO_FULL_LAMBDA_SUPPORT

#endif // UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT_HPP_INCLUDED
