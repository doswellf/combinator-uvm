# /* **************************************************************************
#  *                                                                          *
#  *     (C) Copyright Paul Mensonides 2011.                                  *
#  *     (C) Copyright Edward Diener 2011.                                    *
#  *     Distributed under the Boost Software License, Version 1.0. (See      *
#  *     accompanying file LICENSE_1_0.txt or copy at                         *
#  *     http://www.boost.org/LICENSE_1_0.txt)                                *
#  *                                                                          *
#  ************************************************************************** */
#
# /* See http://www.boost.org for most recent version. */
#
# ifndef UVMSC_BOOST_PREPROCESSOR_FACILITIES_OVERLOAD_HPP
# define UVMSC_BOOST_PREPROCESSOR_FACILITIES_OVERLOAD_HPP
#
# include <packages/boost/include/preprocessor/cat.hpp>
# include <packages/boost/include/preprocessor/variadic/size.hpp>
#
# /* UVMSC_BOOST_PP_OVERLOAD */
#
# if UVMSC_BOOST_PP_VARIADICS
#    define UVMSC_BOOST_PP_OVERLOAD(prefix, ...) UVMSC_BOOST_PP_CAT(prefix, UVMSC_BOOST_PP_VARIADIC_SIZE(__VA_ARGS__))
# endif
#
# endif
