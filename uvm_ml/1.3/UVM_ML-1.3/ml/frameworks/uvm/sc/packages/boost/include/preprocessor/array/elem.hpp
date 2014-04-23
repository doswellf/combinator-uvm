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
# ifndef UVMSC_BOOST_PREPROCESSOR_ARRAY_ELEM_HPP
# define UVMSC_BOOST_PREPROCESSOR_ARRAY_ELEM_HPP
#
# include <packages/boost/include/preprocessor/array/data.hpp>
# include <packages/boost/include/preprocessor/array/size.hpp>
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/tuple/elem.hpp>
#
# /* UVMSC_BOOST_PP_ARRAY_ELEM */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_EDG()
#    define UVMSC_BOOST_PP_ARRAY_ELEM(i, array) UVMSC_BOOST_PP_TUPLE_ELEM(UVMSC_BOOST_PP_ARRAY_SIZE(array), i, UVMSC_BOOST_PP_ARRAY_DATA(array))
# else
#    define UVMSC_BOOST_PP_ARRAY_ELEM(i, array) UVMSC_BOOST_PP_ARRAY_ELEM_I(i, array)
#    define UVMSC_BOOST_PP_ARRAY_ELEM_I(i, array) UVMSC_BOOST_PP_TUPLE_ELEM(UVMSC_BOOST_PP_ARRAY_SIZE(array), i, UVMSC_BOOST_PP_ARRAY_DATA(array))
# endif
#
# endif
