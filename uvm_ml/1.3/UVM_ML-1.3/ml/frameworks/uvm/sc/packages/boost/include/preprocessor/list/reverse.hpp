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
# ifndef UVMSC_BOOST_PREPROCESSOR_LIST_REVERSE_HPP
# define UVMSC_BOOST_PREPROCESSOR_LIST_REVERSE_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/list/fold_left.hpp>
#
# /* UVMSC_BOOST_PP_LIST_REVERSE */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_LIST_REVERSE(list) UVMSC_BOOST_PP_LIST_FOLD_LEFT(UVMSC_BOOST_PP_LIST_REVERSE_O, UVMSC_BOOST_PP_NIL, list)
# else
#    define UVMSC_BOOST_PP_LIST_REVERSE(list) UVMSC_BOOST_PP_LIST_REVERSE_I(list)
#    define UVMSC_BOOST_PP_LIST_REVERSE_I(list) UVMSC_BOOST_PP_LIST_FOLD_LEFT(UVMSC_BOOST_PP_LIST_REVERSE_O, UVMSC_BOOST_PP_NIL, list)
# endif
#
# define UVMSC_BOOST_PP_LIST_REVERSE_O(d, s, x) (x, s)
#
# /* UVMSC_BOOST_PP_LIST_REVERSE_D */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_LIST_REVERSE_D(d, list) UVMSC_BOOST_PP_LIST_FOLD_LEFT_ ## d(UVMSC_BOOST_PP_LIST_REVERSE_O, UVMSC_BOOST_PP_NIL, list)
# else
#    define UVMSC_BOOST_PP_LIST_REVERSE_D(d, list) UVMSC_BOOST_PP_LIST_REVERSE_D_I(d, list)
#    define UVMSC_BOOST_PP_LIST_REVERSE_D_I(d, list) UVMSC_BOOST_PP_LIST_FOLD_LEFT_ ## d(UVMSC_BOOST_PP_LIST_REVERSE_O, UVMSC_BOOST_PP_NIL, list)
# endif
#
# endif
