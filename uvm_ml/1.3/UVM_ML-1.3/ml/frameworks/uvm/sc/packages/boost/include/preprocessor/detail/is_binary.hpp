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
# ifndef UVMSC_BOOST_PREPROCESSOR_DETAIL_IS_BINARY_HPP
# define UVMSC_BOOST_PREPROCESSOR_DETAIL_IS_BINARY_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/detail/check.hpp>
#
# /* UVMSC_BOOST_PP_IS_BINARY */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_IS_BINARY(x) UVMSC_BOOST_PP_CHECK(x, UVMSC_BOOST_PP_IS_BINARY_CHECK)
# else
#    define UVMSC_BOOST_PP_IS_BINARY(x) UVMSC_BOOST_PP_IS_BINARY_I(x)
#    define UVMSC_BOOST_PP_IS_BINARY_I(x) UVMSC_BOOST_PP_CHECK(x, UVMSC_BOOST_PP_IS_BINARY_CHECK)
# endif
#
# define UVMSC_BOOST_PP_IS_BINARY_CHECK(a, b) 1
# define UVMSC_BOOST_PP_CHECK_RESULT_UVMSC_BOOST_PP_IS_BINARY_CHECK 0, UVMSC_BOOST_PP_NIL
#
# endif
