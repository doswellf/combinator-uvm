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
# ifndef UVMSC_BOOST_PREPROCESSOR_PUNCTUATION_COMMA_IF_HPP
# define UVMSC_BOOST_PREPROCESSOR_PUNCTUATION_COMMA_IF_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/control/if.hpp>
# include <packages/boost/include/preprocessor/facilities/empty.hpp>
# include <packages/boost/include/preprocessor/punctuation/comma.hpp>
#
# /* UVMSC_BOOST_PP_COMMA_IF */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_COMMA_IF(cond) UVMSC_BOOST_PP_IF(cond, UVMSC_BOOST_PP_COMMA, UVMSC_BOOST_PP_EMPTY)()
# else
#    define UVMSC_BOOST_PP_COMMA_IF(cond) UVMSC_BOOST_PP_COMMA_IF_I(cond)
#    define UVMSC_BOOST_PP_COMMA_IF_I(cond) UVMSC_BOOST_PP_IF(cond, UVMSC_BOOST_PP_COMMA, UVMSC_BOOST_PP_EMPTY)()
# endif
#
# endif
