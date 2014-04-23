
#ifndef UVMSC_BOOST_MPL_BOOL_HPP_INCLUDED
#define UVMSC_BOOST_MPL_BOOL_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2000-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: bool.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/bool_fwd.hpp>
#include <packages/boost/include/mpl/integral_c_tag.hpp>
#include <packages/boost/include/mpl/aux_/config/static_constant.hpp>

UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE_OPEN

template< bool C_ > struct bool_
{
    UVMSC_BOOST_STATIC_CONSTANT(bool, value = C_);
    typedef integral_c_tag tag;
    typedef bool_ type;
    typedef bool value_type;
    operator bool() const { return this->value; }
};

#if !defined(UVMSC_BOOST_NO_INCLASS_MEMBER_INITIALIZATION)
template< bool C_ >
bool const bool_<C_>::value;
#endif

UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE_CLOSE

#endif // UVMSC_BOOST_MPL_BOOL_HPP_INCLUDED
