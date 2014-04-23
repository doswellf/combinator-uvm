# /* Copyright (C) 2001
#  * Housemarque Oy
#  * http://www.housemarque.com
#  *
#  * Distributed under the Boost Software License, Version 1.0. (See
#  * accompanying file LICENSE_1_0.txt or copy at
#  * http://www.boost.org/LICENSE_1_0.txt)
#  *
#  * See http://www.boost.org for most recent version.
#  */
#
# /* Revised by Paul Mensonides (2002) */
#
# ifndef UVMSC_BOOST_PREPROCESSOR_LIST_ADT_HPP
# define UVMSC_BOOST_PREPROCESSOR_LIST_ADT_HPP
#
# include <packages/boost/include/preprocessor/config/config.hpp>
# include <packages/boost/include/preprocessor/detail/is_binary.hpp>
# include <packages/boost/include/preprocessor/logical/compl.hpp>
# include <packages/boost/include/preprocessor/tuple/eat.hpp>
#
# /* UVMSC_BOOST_PP_LIST_CONS */
#
# define UVMSC_BOOST_PP_LIST_CONS(head, tail) (head, tail)
#
# /* UVMSC_BOOST_PP_LIST_NIL */
#
# define UVMSC_BOOST_PP_LIST_NIL UVMSC_BOOST_PP_NIL
#
# /* UVMSC_BOOST_PP_LIST_FIRST */
#
# define UVMSC_BOOST_PP_LIST_FIRST(list) UVMSC_BOOST_PP_LIST_FIRST_D(list)
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_LIST_FIRST_D(list) UVMSC_BOOST_PP_LIST_FIRST_I list
# else
#    define UVMSC_BOOST_PP_LIST_FIRST_D(list) UVMSC_BOOST_PP_LIST_FIRST_I ## list
# endif
#
# define UVMSC_BOOST_PP_LIST_FIRST_I(head, tail) head
#
# /* UVMSC_BOOST_PP_LIST_REST */
#
# define UVMSC_BOOST_PP_LIST_REST(list) UVMSC_BOOST_PP_LIST_REST_D(list)
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_MWCC()
#    define UVMSC_BOOST_PP_LIST_REST_D(list) UVMSC_BOOST_PP_LIST_REST_I list
# else
#    define UVMSC_BOOST_PP_LIST_REST_D(list) UVMSC_BOOST_PP_LIST_REST_I ## list
# endif
#
# define UVMSC_BOOST_PP_LIST_REST_I(head, tail) tail
#
# /* UVMSC_BOOST_PP_LIST_IS_CONS */
#
# if UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_BCC()
#    define UVMSC_BOOST_PP_LIST_IS_CONS(list) UVMSC_BOOST_PP_LIST_IS_CONS_D(list)
#    define UVMSC_BOOST_PP_LIST_IS_CONS_D(list) UVMSC_BOOST_PP_LIST_IS_CONS_ ## list
#    define UVMSC_BOOST_PP_LIST_IS_CONS_(head, tail) 1
#    define UVMSC_BOOST_PP_LIST_IS_CONS_UVMSC_BOOST_PP_NIL 0
# else
#    define UVMSC_BOOST_PP_LIST_IS_CONS(list) UVMSC_BOOST_PP_IS_BINARY(list)
# endif
#
# /* UVMSC_BOOST_PP_LIST_IS_NIL */
#
# if ~UVMSC_BOOST_PP_CONFIG_FLAGS() & UVMSC_BOOST_PP_CONFIG_BCC()
#    define UVMSC_BOOST_PP_LIST_IS_NIL(list) UVMSC_BOOST_PP_COMPL(UVMSC_BOOST_PP_IS_BINARY(list))
# else
#    define UVMSC_BOOST_PP_LIST_IS_NIL(list) UVMSC_BOOST_PP_COMPL(UVMSC_BOOST_PP_LIST_IS_CONS(list))
# endif
#
# endif
