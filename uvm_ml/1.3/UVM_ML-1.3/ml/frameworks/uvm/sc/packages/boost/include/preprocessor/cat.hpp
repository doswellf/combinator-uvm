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
# ifndef UVMSC_BOOST_PREPROCESSOR_CAT_HPP
# define UVMSC_BOOST_PREPROCESSOR_CAT_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_CAT */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_CAT(a, b) UVMSC_BOOST_PP_CAT_I(a, b)
# else
#    define UVMSC_BOOST_PP_CAT(a, b) UVMSC_BOOST_PP_CAT_OO((a, b))
#    define UVMSC_BOOST_PP_CAT_OO(par) UVMSC_BOOST_PP_CAT_I ## par
# endif
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC()
#    define UVMSC_BOOST_PP_CAT_I(a, b) a ## b
# else
#    define UVMSC_BOOST_PP_CAT_I(a, b) UVMSC_BOOST_PP_CAT_II(~, a ## b)
#    define UVMSC_BOOST_PP_CAT_II(p, res) res
# endif
#
# endif
