
#ifndef UVMSC_BOOST_MPL_NOT_HPP_INCLUDED
#define UVMSC_BOOST_MPL_NOT_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2000-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: not.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/bool.hpp>
#include <packages/boost/include/mpl/aux_/nttp_decl.hpp>
#include <packages/boost/include/mpl/aux_/nested_type_wknd.hpp>
#include <packages/boost/include/mpl/aux_/na_spec.hpp>
#include <packages/boost/include/mpl/aux_/lambda_support.hpp>

namespace uvmsc_boost { namespace mpl {

namespace aux {

template< UVMSC_BOOST_MPL_AUX_NTTP_DECL(long, C_) > // 'long' is intentional here
struct not_impl
    : bool_<!C_>
{
};

} // namespace aux


template<
      typename UVMSC_BOOST_MPL_AUX_NA_PARAM(T)
    >
struct not_
    : aux::not_impl<
          UVMSC_BOOST_MPL_AUX_NESTED_TYPE_WKND(T)::value
        >
{
    UVMSC_BOOST_MPL_AUX_LAMBDA_SUPPORT(1,not_,(T))
};

UVMSC_BOOST_MPL_AUX_NA_SPEC(1,not_)

}}

#endif // UVMSC_BOOST_MPL_NOT_HPP_INCLUDED
