
#ifndef UVMSC_BOOST_MPL_AND_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AND_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2000-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: and.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/use_preprocessed.hpp>

#if !defined(UVMSC_BOOST_MPL_CFG_NO_PREPROCESSED_HEADERS) \
    && !defined(UVMSC_BOOST_MPL_PREPROCESSING_MODE)

#   include <packages/boost/include/mpl/bool.hpp>
#   include <packages/boost/include/mpl/aux_/nested_type_wknd.hpp>
#   include <packages/boost/include/mpl/aux_/na_spec.hpp>
#   include <packages/boost/include/mpl/aux_/lambda_support.hpp>

// agurt, 19/may/04: workaround a conflict with <iso646.h> header's 
// 'or' and 'and' macros, see http://tinyurl.com/3et69; 'defined(and)'
// has to be checked in a separate condition, otherwise GCC complains 
// about 'and' being an alternative token
#if defined(_MSC_VER) 
#ifndef __GCCXML__
#if defined(and) 
#   pragma push_macro("and")
#   undef and
#   define and(x)
#endif
#endif
#endif

#   define UVMSC_BOOST_MPL_PREPROCESSED_HEADER and.hpp
#   include <packages/boost/include/mpl/aux_/include_preprocessed.hpp>

#if defined(_MSC_VER)
#ifndef __GCCXML__
#if defined(and) 
#   pragma pop_macro("and")
#endif
#endif
#endif

#else

#   define AUX778076_OP_NAME and_
#   define AUX778076_OP_VALUE1 false
#   define AUX778076_OP_VALUE2 true
#   include <packages/boost/include/mpl/aux_/logical_op.hpp>

#endif // UVMSC_BOOST_MPL_CFG_NO_PREPROCESSED_HEADERS
#endif // UVMSC_BOOST_MPL_AND_HPP_INCLUDED
