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
# ifndef UVMSC_BOOST_PREPROCESSOR_LOGICAL_COMPL_HPP
# define UVMSC_BOOST_PREPROCESSOR_LOGICAL_COMPL_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_COMPL */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_COMPL(x) UVMSC_BOOST_PP_COMPL_I(x)
# else
#    define UVMSC_BOOST_PP_COMPL(x) UVMSC_BOOST_PP_COMPL_OO((x))
#    define UVMSC_BOOST_PP_COMPL_OO(par) UVMSC_BOOST_PP_COMPL_I ## par
# endif
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC()
#    define UVMSC_BOOST_PP_COMPL_I(x) UVMSC_BOOST_PP_COMPL_ ## x
# else
#    define UVMSC_BOOST_PP_COMPL_I(x) UVMSC_BOOST_PP_COMPL_ID(UVMSC_BOOST_PP_COMPL_ ## x)
#    define UVMSC_BOOST_PP_COMPL_ID(id) id
# endif
#
# define UVMSC_BOOST_PP_COMPL_0 1
# define UVMSC_BOOST_PP_COMPL_1 0
#
# endif
