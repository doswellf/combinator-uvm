# /* Copyright (C) 2001
#  * Housemarque Oy
#  * http://www.housemarque.com
#  *
#  * Distributed under the Boost Software License, Version 1.0. (See
#  * accompanying file LICENSE_1_0.txt or copy at
#  * http://www.boost.org/LICENSE_1_0.txt)
#  */
#
# /* Revised by Paul Mensonides (2002) */
#
# /* See http://www.boost.org for most recent version. */
#
# ifndef UVMSC_BOOST_PREPROCESSOR_STRINGIZE_HPP
# define UVMSC_BOOST_PREPROCESSOR_STRINGIZE_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_STRINGIZE */
#
# if UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC()
#    define UVMSC_BOOST_PP_STRINGIZE(text) UVMSC_BOOST_PP_STRINGIZE_A((text))
#    define UVMSC_BOOST_PP_STRINGIZE_A(arg) UVMSC_BOOST_PP_STRINGIZE_I arg
# elif UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_STRINGIZE(text) UVMSC_BOOST_PP_STRINGIZE_OO((text))
#    define UVMSC_BOOST_PP_STRINGIZE_OO(par) UVMSC_BOOST_PP_STRINGIZE_I ## par
# else
#    define UVMSC_BOOST_PP_STRINGIZE(text) UVMSC_BOOST_PP_STRINGIZE_I(text)
# endif
#
# define UVMSC_BOOST_PP_STRINGIZE_I(text) #text
#
# endif
