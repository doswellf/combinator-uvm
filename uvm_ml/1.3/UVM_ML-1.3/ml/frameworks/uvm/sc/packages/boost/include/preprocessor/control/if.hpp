# /* Copyright (C) 2001
#  * Housemarque Oy
#  * http://www.housemarque.com
#  *
#  * Distributed under the Boost Software License, Version 1.0. (See
#  * accompanying file LICENSE_1_0.txt or copy at
#  * http://www.boost.org/LICENSE_1_0.txt)
#  */
#
# /* Revised by Paul Mensonides (2002) */
#
# /* See http://www.boost.org for most recent version. */
#
# ifndef UVMSC_BOOST_PREPROCESSOR_CONTROL_IF_HPP
# define UVMSC_BOOST_PREPROCESSOR_CONTROL_IF_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/control/iif.hpp>
# include <packages/boost/include/preprocessor/logical/bool.hpp>
#
# /* UVMSC_BOOST_PP_IF */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_IF(cond, t, f) UVMSC_BOOST_PP_IIF(UVMSC_BOOST_PP_BOOL(cond), t, f)
# else
#    define UVMSC_BOOST_PP_IF(cond, t, f) UVMSC_BOOST_PP_IF_I(cond, t, f)
#    define UVMSC_BOOST_PP_IF_I(cond, t, f) UVMSC_BOOST_PP_IIF(UVMSC_BOOST_PP_BOOL(cond), t, f)
# endif
#
# endif
