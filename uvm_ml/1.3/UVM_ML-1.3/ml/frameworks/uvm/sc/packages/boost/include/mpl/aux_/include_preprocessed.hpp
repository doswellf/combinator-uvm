
// NO INCLUDE GUARDS, THE HEADER IS INTENDED FOR MULTIPLE INCLUSION

// Copyright Aleksey Gurtovoy 2000-2006
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: include_preprocessed.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/compiler.hpp>
#include <packages/boost/include/mpl/aux_/config/preprocessor.hpp>
#include <packages/boost/include/mpl/aux_/config/workaround.hpp>
#include <packages/boost/include/preprocessor/cat.hpp>
#include <packages/boost/include/preprocessor/stringize.hpp>

#if !defined(UVMSC_BOOST_NEEDS_TOKEN_PASTING_OP_FOR_TOKENS_JUXTAPOSING)
#   define AUX778076_PREPROCESSED_HEADER \
    UVMSC_BOOST_MPL_CFG_COMPILER_DIR/UVMSC_BOOST_MPL_PREPROCESSED_HEADER \
/**/
#else
#   define AUX778076_PREPROCESSED_HEADER \
    UVMSC_BOOST_PP_CAT(UVMSC_BOOST_MPL_CFG_COMPILER_DIR,/)##UVMSC_BOOST_MPL_PREPROCESSED_HEADER \
/**/
#endif

#if UVMSC_BOOST_WORKAROUND(__IBMCPP__, UVMSC_BOOST_TESTED_AT(700))
#   define AUX778076_INCLUDE_STRING UVMSC_BOOST_PP_STRINGIZE(packages/boost/include/mpl/aux_/preprocessed/AUX778076_PREPROCESSED_HEADER)
#   include AUX778076_INCLUDE_STRING
#   undef AUX778076_INCLUDE_STRING
#else
#   include UVMSC_BOOST_PP_STRINGIZE(packages/boost/include/mpl/aux_/preprocessed/AUX778076_PREPROCESSED_HEADER)
#endif

#   undef AUX778076_PREPROCESSED_HEADER

#undef UVMSC_BOOST_MPL_PREPROCESSED_HEADER
