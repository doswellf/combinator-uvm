# /* **************************************************************************
#  *                                                                          *
#  *     (C) Copyright Paul Mensonides 2002.
#  *     Distributed under the Boost Software License, Version 1.0. (See
#  *     accompanying file LICENSE_1_0.txt or copy at
#  *     http://www.boost.org/LICENSE_1_0.txt)
#  *                                                                          *
#  ************************************************************************** */
#
# /* See http://www.boost.org for most recent version. */
#
# ifndef UVMSC_BOOST_PREPROCESSOR_LOGICAL_BITAND_HPP
# define UVMSC_BOOST_PREPROCESSOR_LOGICAL_BITAND_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_BITAND */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_BITAND(x, y) UVMSC_BOOST_PP_BITAND_I(x, y)
# else
#    define UVMSC_BOOST_PP_BITAND(x, y) UVMSC_BOOST_PP_BITAND_OO((x, y))
#    define UVMSC_BOOST_PP_BITAND_OO(par) UVMSC_BOOST_PP_BITAND_I ## par
# endif
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC()
#    define UVMSC_BOOST_PP_BITAND_I(x, y) UVMSC_BOOST_PP_BITAND_ ## x ## y
# else
#    define UVMSC_BOOST_PP_BITAND_I(x, y) UVMSC_BOOST_PP_BITAND_ID(UVMSC_BOOST_PP_BITAND_ ## x ## y)
#    define UVMSC_BOOST_PP_BITAND_ID(res) res
# endif
#
# define UVMSC_BOOST_PP_BITAND_00 0
# define UVMSC_BOOST_PP_BITAND_01 0
# define UVMSC_BOOST_PP_BITAND_10 0
# define UVMSC_BOOST_PP_BITAND_11 1
#
# endif
