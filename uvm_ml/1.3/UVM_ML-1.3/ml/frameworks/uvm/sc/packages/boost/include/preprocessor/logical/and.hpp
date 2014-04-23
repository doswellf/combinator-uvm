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
# ifndef UVMSC_BOOST_PREPROCESSOR_LOGICAL_AND_HPP
# define UVMSC_BOOST_PREPROCESSOR_LOGICAL_AND_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/logical/bool.hpp>
# include <packages/boost/include/preprocessor/logical/bitand.hpp>
#
# /* UVMSC_BOOST_PP_AND */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_AND(p, q) UVMSC_BOOST_PP_BITAND(UVMSC_BOOST_PP_BOOL(p), UVMSC_BOOST_PP_BOOL(q))
# else
#    define UVMSC_BOOST_PP_AND(p, q) UVMSC_BOOST_PP_AND_I(p, q)
#    define UVMSC_BOOST_PP_AND_I(p, q) UVMSC_BOOST_PP_BITAND(UVMSC_BOOST_PP_BOOL(p), UVMSC_BOOST_PP_BOOL(q))
# endif
#
# endif
