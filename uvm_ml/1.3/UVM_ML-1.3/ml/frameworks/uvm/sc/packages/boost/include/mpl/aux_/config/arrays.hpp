
#ifndef UVMSC_BOOST_MPL_AUX_CONFIG_ARRAYS_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_CONFIG_ARRAYS_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2003-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: arrays.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/msvc.hpp>
#include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#if    !defined(UVMSC_BOOST_MPL_CFG_NO_DEPENDENT_ARRAY_TYPES) \
    && !defined(UVMSC_BOOST_MPL_PREPROCESSING_MODE) \
    && ( UVMSC_BOOST_WORKAROUND(__BORLANDC__, UVMSC_BOOST_TESTED_AT(0x610)) \
        || UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, <= 1300) \
        )

#   define UVMSC_BOOST_MPL_CFG_NO_DEPENDENT_ARRAY_TYPES

#endif

#endif // UVMSC_BOOST_MPL_AUX_CONFIG_ARRAYS_HPP_INCLUDED
