
#ifndef UVMSC_BOOST_MPL_AUX_PREPROCESSOR_DEF_PARAMS_TAIL_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_PREPROCESSOR_DEF_PARAMS_TAIL_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2000-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: def_params_tail.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/limits/arity.hpp>
#include <packages/boost/include/mpl/aux_/config/dtp.hpp>
#include <packages/boost/include/mpl/aux_/config/preprocessor.hpp>

#include <packages/boost/include/preprocessor/comma_if.hpp>
#include <packages/boost/include/preprocessor/logical/and.hpp>
#include <packages/boost/include/preprocessor/identity.hpp>
#include <packages/boost/include/preprocessor/empty.hpp>

// UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL(1,T,value): , T1 = value, .., Tn = value
// UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL(2,T,value): , T2 = value, .., Tn = value
// UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL(n,T,value): <nothing>

#if !defined(UVMSC_BOOST_MPL_CFG_NO_OWN_PP_PRIMITIVES)

#   include <packages/boost/include/mpl/aux_/preprocessor/filter_params.hpp>
#   include <packages/boost/include/mpl/aux_/preprocessor/sub.hpp>

#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_IMPL(i, param, value_func) \
    UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_DELAY_1( \
          i \
        , UVMSC_BOOST_MPL_PP_SUB(UVMSC_BOOST_MPL_LIMIT_METAFUNCTION_ARITY,i) \
        , param \
        , value_func \
        ) \
    /**/

#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_DELAY_1(i, n, param, value_func) \
    UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_DELAY_2(i,n,param,value_func) \
    /**/

#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_DELAY_2(i, n, param, value_func) \
    UVMSC_BOOST_PP_COMMA_IF(UVMSC_BOOST_PP_AND(i,n)) \
    UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_##i(n,param,value_func) \
    /**/

#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_0(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##1 v(),p##2 v(),p##3 v(),p##4 v(),p##5 v(),p##6 v(),p##7 v(),p##8 v(),p##9 v())
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_1(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##2 v(),p##3 v(),p##4 v(),p##5 v(),p##6 v(),p##7 v(),p##8 v(),p##9 v(),p1)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_2(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##3 v(),p##4 v(),p##5 v(),p##6 v(),p##7 v(),p##8 v(),p##9 v(),p1,p2)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_3(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##4 v(),p##5 v(),p##6 v(),p##7 v(),p##8 v(),p##9 v(),p1,p2,p3)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_4(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##5 v(),p##6 v(),p##7 v(),p##8 v(),p##9 v(),p1,p2,p3,p4)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_5(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##6 v(),p##7 v(),p##8 v(),p##9 v(),p1,p2,p3,p4,p5)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_6(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##7 v(),p##8 v(),p##9 v(),p1,p2,p3,p4,p5,p6)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_7(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##8 v(),p##9 v(),p1,p2,p3,p4,p5,p6,p7)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_8(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p##9 v(),p1,p2,p3,p4,p5,p6,p7,p8)
#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_9(i,p,v) UVMSC_BOOST_MPL_PP_FILTER_PARAMS_##i(p1,p2,p3,p4,p5,p6,p7,p8,p9)

#else

#   include <packages/boost/include/preprocessor/arithmetic/add.hpp>
#   include <packages/boost/include/preprocessor/arithmetic/sub.hpp>
#   include <packages/boost/include/preprocessor/inc.hpp>
#   include <packages/boost/include/preprocessor/tuple/elem.hpp>
#   include <packages/boost/include/preprocessor/repeat.hpp>
#   include <packages/boost/include/preprocessor/cat.hpp>

#   define UVMSC_BOOST_MPL_PP_AUX_TAIL_PARAM_FUNC(unused, i, op) \
    , UVMSC_BOOST_PP_CAT( \
          UVMSC_BOOST_PP_TUPLE_ELEM(3, 1, op) \
        , UVMSC_BOOST_PP_ADD_D(1, i, UVMSC_BOOST_PP_INC(UVMSC_BOOST_PP_TUPLE_ELEM(3, 0, op))) \
        ) UVMSC_BOOST_PP_TUPLE_ELEM(3, 2, op)() \
    /**/

#   define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_IMPL(i, param, value_func) \
    UVMSC_BOOST_PP_REPEAT( \
          UVMSC_BOOST_PP_SUB_D(1, UVMSC_BOOST_MPL_LIMIT_METAFUNCTION_ARITY, i) \
        , UVMSC_BOOST_MPL_PP_AUX_TAIL_PARAM_FUNC \
        , (i, param, value_func) \
        ) \
    /**/


#endif // UVMSC_BOOST_MPL_CFG_NO_OWN_PP_PRIMITIVES

#define UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL(i, param, value) \
    UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_IMPL(i, param, UVMSC_BOOST_PP_IDENTITY(=value)) \
    /**/

#if !defined(UVMSC_BOOST_MPL_CFG_NO_DEFAULT_PARAMETERS_IN_NESTED_TEMPLATES)
#   define UVMSC_BOOST_MPL_PP_NESTED_DEF_PARAMS_TAIL(i, param, value) \
    UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_IMPL(i, param, UVMSC_BOOST_PP_IDENTITY(=value)) \
    /**/
#else
#   define UVMSC_BOOST_MPL_PP_NESTED_DEF_PARAMS_TAIL(i, param, value) \
    UVMSC_BOOST_MPL_PP_DEF_PARAMS_TAIL_IMPL(i, param, UVMSC_BOOST_PP_EMPTY) \
    /**/
#endif

#endif // UVMSC_BOOST_MPL_AUX_PREPROCESSOR_DEF_PARAMS_TAIL_HPP_INCLUDED
