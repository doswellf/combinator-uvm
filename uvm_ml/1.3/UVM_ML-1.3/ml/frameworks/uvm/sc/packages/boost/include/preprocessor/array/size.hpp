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
# ifndef UVMSC_BOOST_PREPROCESSOR_ARRAY_SIZE_HPP
# define UVMSC_BOOST_PREPROCESSOR_ARRAY_SIZE_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/tuple/elem.hpp>
#
# /* UVMSC_BOOST_PP_ARRAY_SIZE */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_ARRAY_SIZE(array) UVMSC_BOOST_PP_TUPLE_ELEM(2, 0, array)
# else
#    define UVMSC_BOOST_PP_ARRAY_SIZE(array) UVMSC_BOOST_PP_ARRAY_SIZE_I(array)
#    define UVMSC_BOOST_PP_ARRAY_SIZE_I(array) UVMSC_BOOST_PP_ARRAY_SIZE_II array
#    define UVMSC_BOOST_PP_ARRAY_SIZE_II(size, data) size
# endif
#
# endif
