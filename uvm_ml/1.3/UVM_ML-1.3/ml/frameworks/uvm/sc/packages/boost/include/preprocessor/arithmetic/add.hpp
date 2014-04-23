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
# ifndef UVMSC_BOOST_PREPROCESSOR_ARITHMETIC_ADD_HPP
# define UVMSC_BOOST_PREPROCESSOR_ARITHMETIC_ADD_HPP
#
# include <packages/boost/include/preprocessor/arithmetic/dec.hpp>
# include <packages/boost/include/preprocessor/arithmetic/inc.hpp>
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/control/while.hpp>
# include <packages/boost/include/preprocessor/tuple/elem.hpp>
#
# /* UVMSC_BOOST_PP_ADD */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_ADD(x, y) UVMSC_BOOST_PP_TUPLE_ELEM(2, 0, UVMSC_BOOST_PP_WHILE(UVMSC_BOOST_PP_ADD_P, UVMSC_BOOST_PP_ADD_O, (x, y)))
# else
#    define UVMSC_BOOST_PP_ADD(x, y) UVMSC_BOOST_PP_ADD_I(x, y)
#    define UVMSC_BOOST_PP_ADD_I(x, y) UVMSC_BOOST_PP_TUPLE_ELEM(2, 0, UVMSC_BOOST_PP_WHILE(UVMSC_BOOST_PP_ADD_P, UVMSC_BOOST_PP_ADD_O, (x, y)))
# endif
#
# define UVMSC_BOOST_PP_ADD_P(d, xy) UVMSC_BOOST_PP_TUPLE_ELEM(2, 1, xy)
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_ADD_O(d, xy) UVMSC_BOOST_PP_ADD_O_I xy
# else
#    define UVMSC_BOOST_PP_ADD_O(d, xy) UVMSC_BOOST_PP_ADD_O_I(UVMSC_BOOST_PP_TUPLE_ELEM(2, 0, xy), UVMSC_BOOST_PP_TUPLE_ELEM(2, 1, xy))
# endif
#
# define UVMSC_BOOST_PP_ADD_O_I(x, y) (UVMSC_BOOST_PP_INC(x), UVMSC_BOOST_PP_DEC(y))
#
# /* UVMSC_BOOST_PP_ADD_D */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_ADD_D(d, x, y) UVMSC_BOOST_PP_TUPLE_ELEM(2, 0, UVMSC_BOOST_PP_WHILE_ ## d(UVMSC_BOOST_PP_ADD_P, UVMSC_BOOST_PP_ADD_O, (x, y)))
# else
#    define UVMSC_BOOST_PP_ADD_D(d, x, y) UVMSC_BOOST_PP_ADD_D_I(d, x, y)
#    define UVMSC_BOOST_PP_ADD_D_I(d, x, y) UVMSC_BOOST_PP_TUPLE_ELEM(2, 0, UVMSC_BOOST_PP_WHILE_ ## d(UVMSC_BOOST_PP_ADD_P, UVMSC_BOOST_PP_ADD_O, (x, y)))
# endif
#
# endif
