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
# ifndef UVMSC_BOOST_PREPROCESSOR_LIST_FOLD_RIGHT_HPP
# define UVMSC_BOOST_PREPROCESSOR_LIST_FOLD_RIGHT_HPP
#
# include <packages/boost/include/preprocessor/cat.hpp>
# include <packages/boost/include/preprocessor/control/while.hpp>
# include <packages/boost/include/preprocessor/debug/error.hpp>
# include <packages/boost/include/preprocessor/detail/auto_rec.hpp>
#
# if 0
#    define UVMSC_BOOST_PP_LIST_FOLD_RIGHT(op, state, list)
# endif
#
# define UVMSC_BOOST_PP_LIST_FOLD_RIGHT UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_LIST_FOLD_RIGHT_, UVMSC_BOOST_PP_AUTO_REC(UVMSC_BOOST_PP_WHILE_P, 256))
#
# define UVMSC_BOOST_PP_LIST_FOLD_RIGHT_257(o, s, l) UVMSC_BOOST_PP_ERROR(0x0004)
#
# define UVMSC_BOOST_PP_LIST_FOLD_RIGHT_D(d, o, s, l) UVMSC_BOOST_PP_LIST_FOLD_RIGHT_ ## d(o, s, l)
# define UVMSC_BOOST_PP_LIST_FOLD_RIGHT_2ND UVMSC_BOOST_PP_LIST_FOLD_RIGHT
# define UVMSC_BOOST_PP_LIST_FOLD_RIGHT_2ND_D UVMSC_BOOST_PP_LIST_FOLD_RIGHT_D
#
# if UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    include <packages/boost/include/preprocessor/list/detail/edg/fold_right.hpp>
# else
#    include <packages/boost/include/preprocessor/list/detail/fold_right.hpp>
# endif
#
# endif
