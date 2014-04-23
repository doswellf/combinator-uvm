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
# ifndef UVMSC_BOOST_PREPROCESSOR_CONTROL_IIF_HPP
# define UVMSC_BOOST_PREPROCESSOR_CONTROL_IIF_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_IIF(bit, t, f) UVMSC_BOOST_PP_IIF_I(bit, t, f)
# else
#    define UVMSC_BOOST_PP_IIF(bit, t, f) UVMSC_BOOST_PP_IIF_OO((bit, t, f))
#    define UVMSC_BOOST_PP_IIF_OO(par) UVMSC_BOOST_PP_IIF_I ## par
# endif
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC()
#    define UVMSC_BOOST_PP_IIF_I(bit, t, f) UVMSC_BOOST_PP_IIF_ ## bit(t, f)
# else
#    define UVMSC_BOOST_PP_IIF_I(bit, t, f) UVMSC_BOOST_PP_IIF_II(UVMSC_BOOST_PP_IIF_ ## bit(t, f))
#    define UVMSC_BOOST_PP_IIF_II(id) id
# endif
#
# define UVMSC_BOOST_PP_IIF_0(t, f) f
# define UVMSC_BOOST_PP_IIF_1(t, f) t
#
# endif
