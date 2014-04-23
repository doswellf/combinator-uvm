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
# ifndef UVMSC_BOOST_PREPROCESSOR_REPETITION_ENUM_TRAILING_PARAMS_HPP
# define UVMSC_BOOST_PREPROCESSOR_REPETITION_ENUM_TRAILING_PARAMS_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/repetition/repeat.hpp>
#
# /* UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS(count, param) UVMSC_BOOST_PP_REPEAT(count, UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_M, param)
# else
#    define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS(count, param) UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_I(count, param)
#    define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_I(count, param) UVMSC_BOOST_PP_REPEAT(count, UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_M, param)
# endif
#
# define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_M(z, n, param) , param ## n
#
# /* UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_Z */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_Z(z, count, param) UVMSC_BOOST_PP_REPEAT_ ## z(count, UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_M, param)
# else
#    define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_Z(z, count, param) UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_Z_I(z, count, param)
#    define UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_Z_I(z, count, param) UVMSC_BOOST_PP_REPEAT_ ## z(count, UVMSC_BOOST_PP_ENUM_TRAILING_PARAMS_M, param)
# endif
#
# endif
