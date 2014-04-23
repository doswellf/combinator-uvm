
#ifndef UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2000-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: nested_type_wknd.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/gcc.hpp>
#include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MPL_CFG_GCC, UVMSC_BOOST_TESTED_AT(0x0302)) \
    || UVMSC_BOOST_WORKAROUND(__BORLANDC__, UVMSC_BOOST_TESTED_AT(0x561)) \
    || UVMSC_BOOST_WORKAROUND(__SUNPRO_CC, UVMSC_BOOST_TESTED_AT(0x530)) \
    || UVMSC_BOOST_WORKAROUND(__DMC__, UVMSC_BOOST_TESTED_AT(0x840))

namespace uvmsc_boost { namespace mpl { namespace aux {
template< typename T > struct nested_type_wknd
    : T::type
{
};
}}}

#if UVMSC_BOOST_WORKAROUND(__DMC__, UVMSC_BOOST_TESTED_AT(0x840))
#   define UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND(T) \
    aux::nested_type_wknd<T> \
/**/
#else
#   define UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND(T) \
    ::uvmsc_boost::mpl::aux::nested_type_wknd<T> \
/**/
#endif

#else // !UVMSC_BOOST_MPL_CFG_GCC et al.

#   define UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND(T) T::type

#endif 

#endif // UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND_HPP_INCLUDED
