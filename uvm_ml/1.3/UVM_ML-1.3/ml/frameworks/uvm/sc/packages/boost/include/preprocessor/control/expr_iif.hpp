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
# ifndef UVMSC_BOOST_PREPROCESSOR_CONTROL_EXPR_IIF_HPP
# define UVMSC_BOOST_PREPROCESSOR_CONTROL_EXPR_IIF_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_EXPR_IIF */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_EXPR_IIF(bit, expr) UVMSC_BOOST_PP_EXPR_IIF_I(bit, expr)
# else
#    define UVMSC_BOOST_PP_EXPR_IIF(bit, expr) UVMSC_BOOST_PP_EXPR_IIF_OO((bit, expr))
#    define UVMSC_BOOST_PP_EXPR_IIF_OO(par) UVMSC_BOOST_PP_EXPR_IIF_I ## par
# endif
#
# define UVMSC_BOOST_PP_EXPR_IIF_I(bit, expr) UVMSC_BOOST_PP_EXPR_IIF_ ## bit(expr)
#
# define UVMSC_BOOST_PP_EXPR_IIF_0(expr)
# define UVMSC_BOOST_PP_EXPR_IIF_1(expr) expr
#
# endif
