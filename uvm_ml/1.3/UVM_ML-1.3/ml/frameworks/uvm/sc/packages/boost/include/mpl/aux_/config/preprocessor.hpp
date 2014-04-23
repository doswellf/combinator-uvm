
#ifndef UVMSC_BOOST_MPL_AUX_CONFIG_PREPROCESSOR_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_CONFIG_PREPROCESSOR_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2000-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: preprocessor.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#if !defined(UVMSC_BOOST_MPL_CFG_BROKEN_PP_MACRO_EXPANSION) \
    && (   UVMSC_BOOST_WORKAROUND(__MWERKS__, <= 0x3003) \
        || UVMSC_BOOST_WORKAROUND(__BORLANDC__, < 0x582) \
        || UVMSC_BOOST_WORKAROUND(__IBMCPP__, UVMSC_BOOST_TESTED_AT(502)) \
        )

#   define UVMSC_BOOST_MPL_CFG_BROKEN_PP_MACRO_EXPANSION

#endif

#if !defined(UVMSC_BOOST_MPL_CFG_NO_OWN_PP_PRIMITIVES)
#   define UVMSC_BOOST_MPL_CFG_NO_OWN_PP_PRIMITIVES
#endif

#if !defined(UVMSC_BOOST_NEEDS_TOKEN_PASTING_OP_FOR_TOKENS_JUXTAPOSING) \
    && UVMSC_BOOST_WORKAROUND(__DMC__, UVMSC_BOOST_TESTED_AT(0x840))
#   define UVMSC_BOOST_NEEDS_TOKEN_PASTING_OP_FOR_TOKENS_JUXTAPOSING
#endif


#endif // UVMSC_BOOST_MPL_AUX_CONFIG_PREPROCESSOR_HPP_INCLUDED
