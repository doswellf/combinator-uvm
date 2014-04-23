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
# ifndef UVMSC_BOOST_PREPROCESSOR_DETAIL_CHECK_HPP
# define UVMSC_BOOST_PREPROCESSOR_DETAIL_CHECK_HPP
#
# include <packages/boost/include/preprocessor/cat.hpp>
# include <packages/boost/include/preprocessor/config/config.hpp>
#
# /* UVMSC_BOOST_PP_CHECK */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_CHECK(x, type) UVMSC_BOOST_PP_CHECK_D(x, type)
# else
#    define UVMSC_BOOST_PP_CHECK(x, type) UVMSC_BOOST_PP_CHECK_OO((x, type))
#    define UVMSC_BOOST_PP_CHECK_OO(par) UVMSC_BOOST_PP_CHECK_D ## par
# endif
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC() && ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_DMC()
#    define UVMSC_BOOST_PP_CHECK_D(x, type) UVMSC_BOOST_PP_CHECK_1(UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_CHECK_RESULT_, type x))
#    define UVMSC_BOOST_PP_CHECK_1(chk) UVMSC_BOOST_PP_CHECK_2(chk)
#    define UVMSC_BOOST_PP_CHECK_2(res, _) res
# elif UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MSVC()
#    define UVMSC_BOOST_PP_CHECK_D(x, type) UVMSC_BOOST_PP_CHECK_1(type x)
#    define UVMSC_BOOST_PP_CHECK_1(chk) UVMSC_BOOST_PP_CHECK_2(chk)
#    define UVMSC_BOOST_PP_CHECK_2(chk) UVMSC_BOOST_PP_CHECK_3((UVMSC_BOOST_PP_CHECK_RESULT_ ## chk))
#    define UVMSC_BOOST_PP_CHECK_3(im) UVMSC_BOOST_PP_CHECK_5(UVMSC_BOOST_PP_CHECK_4 im)
#    define UVMSC_BOOST_PP_CHECK_4(res, _) res
#    define UVMSC_BOOST_PP_CHECK_5(res) res
# else /* DMC */
#    define UVMSC_BOOST_PP_CHECK_D(x, type) UVMSC_BOOST_PP_CHECK_OO((type x))
#    define UVMSC_BOOST_PP_CHECK_OO(par) UVMSC_BOOST_PP_CHECK_0 ## par
#    define UVMSC_BOOST_PP_CHECK_0(chk) UVMSC_BOOST_PP_CHECK_1(UVMSC_BOOST_PP_CAT(UVMSC_BOOST_PP_CHECK_RESULT_, chk))
#    define UVMSC_BOOST_PP_CHECK_1(chk) UVMSC_BOOST_PP_CHECK_2(chk)
#    define UVMSC_BOOST_PP_CHECK_2(res, _) res
# endif
#
# define UVMSC_BOOST_PP_CHECK_RESULT_1 1, UVMSC_BOOST_PP_NIL
#
# endif
