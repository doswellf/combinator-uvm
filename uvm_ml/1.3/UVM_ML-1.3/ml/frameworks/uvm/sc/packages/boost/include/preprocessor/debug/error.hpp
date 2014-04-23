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
# ifndef UVMSC_BOOST_PREPROCESSOR_DEBUG_ERROR_HPP
# define UVMSC_BOOST_PREPROCESSOR_DEBUG_ERROR_HPP
#
# include <packages/boost/include/preprocessor/cat.hpp>
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_ERROR */
#
# if UVMSC_BOOST_PP_CONFIG_ERRORS
#    define UVMSC_BOOST_PP_ERROR(code) UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_ERROR_, code)
# endif
#
# define UVMSC_BOOST_PP_ERROR_0x0000 UVMSC_BOOST_PP_ERROR(0x0000, UVMSC_BOOST_PP_INDEX_OUT_OF_BOUNDS)
# define UVMSC_BOOST_PP_ERROR_0x0001 UVMSC_BOOST_PP_ERROR(0x0001, UVMSC_BOOST_PP_WHILE_OVERFLOW)
# define UVMSC_BOOST_PP_ERROR_0x0002 UVMSC_BOOST_PP_ERROR(0x0002, UVMSC_BOOST_PP_FOR_OVERFLOW)
# define UVMSC_BOOST_PP_ERROR_0x0003 UVMSC_BOOST_PP_ERROR(0x0003, UVMSC_BOOST_PP_REPEAT_OVERFLOW)
# define UVMSC_BOOST_PP_ERROR_0x0004 UVMSC_BOOST_PP_ERROR(0x0004, UVMSC_BOOST_PP_LIST_FOLD_OVERFLOW)
# define UVMSC_BOOST_PP_ERROR_0x0005 UVMSC_BOOST_PP_ERROR(0x0005, UVMSC_BOOST_PP_SEQ_FOLD_OVERFLOW)
# define UVMSC_BOOST_PP_ERROR_0x0006 UVMSC_BOOST_PP_ERROR(0x0006, UVMSC_BOOST_PP_ARITHMETIC_OVERFLOW)
# define UVMSC_BOOST_PP_ERROR_0x0007 UVMSC_BOOST_PP_ERROR(0x0007, UVMSC_BOOST_PP_DIVISION_BY_ZERO)
#
# endif
