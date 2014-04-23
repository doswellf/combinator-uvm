
#ifndef UVMSC_BOOST_MPL_AUX_CONFIG_COMPILER_HPP_INCLUDED
#define UVMSC_BOOST_MPL_AUX_CONFIG_COMPILER_HPP_INCLUDED

// Copyright Aleksey Gurtovoy 2001-2008
//
// Distributed under the Boost Software License, Version 1.0. 
// (See accompanying file LICENSE_1_0.txt or copy at 
// http://www.boost.org/LICENSE_1_0.txt)
//
// See http://www.boost.org/libs/mpl for documentation.

// $Id: compiler.hpp 53189 2009-05-22 20:07:55Z hkaiser $
// $Date: 2009-05-22 16:07:55 -0400 (Fri, 22 May 2009) $
// $Revision: 53189 $

#if !defined(UVMSC_BOOST_MPL_CFG_COMPILER_DIR)

#   include <packages/boost/include/mpl/aux_/config/dtp.hpp>
#   include <packages/boost/include/mpl/aux_/config/ttp.hpp>
#   include <packages/boost/include/mpl/aux_/config/ctps.hpp>
#   include <packages/boost/include/mpl/aux_/config/msvc.hpp>
#   include <packages/boost/include/mpl/aux_/config/gcc.hpp>
#   include <packages/boost/include/mpl/aux_/config/workaround.hpp>

#   if UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, < 1300)
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR msvc60

#   elif UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, == 1300)
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR msvc70

#   elif UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MPL_CFG_GCC, UVMSC_BOOST_TESTED_AT(0x0304))
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR gcc

#   elif UVMSC_BOOST_WORKAROUND(__BORLANDC__, UVMSC_BOOST_TESTED_AT(0x610))
#       if !defined(UVMSC_BOOST_MPL_CFG_NO_DEFAULT_PARAMETERS_IN_NESTED_TEMPLATES)
#           define UVMSC_BOOST_MPL_CFG_COMPILER_DIR bcc551
#       elif UVMSC_BOOST_WORKAROUND(__BORLANDC__, >= 0x590)
#           define UVMSC_BOOST_MPL_CFG_COMPILER_DIR bcc
#       else
#           define UVMSC_BOOST_MPL_CFG_COMPILER_DIR bcc_pre590
#       endif

#   elif UVMSC_BOOST_WORKAROUND(__DMC__, UVMSC_BOOST_TESTED_AT(0x840))
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR dmc

#   elif defined(__MWERKS__)
#       if defined(UVMSC_BOOST_MPL_CFG_BROKEN_DEFAULT_PARAMETERS_IN_NESTED_TEMPLATES)
#           define UVMSC_BOOST_MPL_CFG_COMPILER_DIR mwcw
#       else
#           define UVMSC_BOOST_MPL_CFG_COMPILER_DIR plain
#       endif

#   elif defined(UVMSC_BOOST_NO_TEMPLATE_PARTIAL_SPECIALIZATION)
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR no_ctps

#   elif defined(UVMSC_BOOST_MPL_CFG_NO_TEMPLATE_TEMPLATE_PARAMETERS)
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR no_ttp

#   else
#       define UVMSC_BOOST_MPL_CFG_COMPILER_DIR plain
#   endif

#endif // UVMSC_BOOST_MPL_CFG_COMPILER_DIR

#endif // UVMSC_BOOST_MPL_AUX_CONFIG_COMPILER_HPP_INCLUDED
