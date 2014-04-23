
#ifndef UVMSC_BOOST_MPL_AUX_ADL_BARRIER_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2002-2004
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: adl_barrier.hpp 49267 2008-10-11 06:19:02Z agurtovoy $
// $Date: 2008-10-11 02:19:02 -0400 (Sat, 11 Oct 2008) $
// $Revision: 49267 $

#include <packages/boost/include/mpl/aux_/config/adl.hpp>
#include <packages/boost/include/mpl/aux_/config/gcc.hpp>
#include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#if !defined(UVMSC_BOOST_MPL_CFG_NO_ADL_BARRIER_NAMESPACE)

#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE uvmsc_boost_mpl_
#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE_OPEN namespace uvmsc_boost_mpl_ {
#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE_CLOSE }
#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_DECL(type) \
    namespace uvmsc_boost { namespace mpl { \
    using ::UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE::type; \
    } } \
/**/

#if !defined(UVMSC_BOOST_MPL_PREPROCESSING_MODE)
namespace UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE { namespace aux {} }
namespace uvmsc_boost { namespace mpl { using namespace UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE; 
namespace aux { using namespace UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE::aux; }
}}
#endif

#else // UVMSC_BOOST_MPL_CFG_NO_ADL_BARRIER_NAMESPACE

#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE uvmsc_boost::mpl
#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE_OPEN namespace uvmsc_boost { namespace mpl {
#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_NAMESPACE_CLOSE }}
#   define UVMSC_BOOST_MPL_AUX_ADL_BARRIER_DECL(type) /**/

#endif

#endif // UVMSC_BOOST_MPL_AUX_ADL_BARRIER_HPP_INCLUDED
