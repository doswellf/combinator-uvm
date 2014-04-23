#ifndef UVMSC_BOOST_THROW_EXCEPTION_HPP_INCLUDED
#define UVMSC_BOOST_THROW_EXCEPTION_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

//
//  packages/boost/include/throw_exception.hpp
//
//  Copyright (c) 2002 Peter Dimov and Multi Media Ltd.
//  Copyright (c) 2008-2009 Emil Dotchevski and Reverge Studios, Inc.
//
//  Distributed under the Boost Software License, Version 1.0. (See
//  accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt)
//
//  http://www.boost.org/libs/utility/throw_exception.html
//

#include <packages/boost/include/exception/detail/attribute_noreturn.hpp>
#include <packages/boost/include/detail/workaround.hpp>
#include <packages/boost/include/config.hpp>
#include <exception>

#if !defined( UVMSC_BOOST_EXCEPTION_DISABLE ) && defined( __BORLANDC__ ) && UVMSC_BOOST_WORKAROUND( __BORLANDC__, UVMSC_BOOST_TESTED_AT(0x593) )
# define UVMSC_BOOST_EXCEPTION_DISABLE
#endif

#if !defined( UVMSC_BOOST_EXCEPTION_DISABLE ) && defined( UVMSC_BOOST_MSVC ) && UVMSC_BOOST_WORKAROUND( UVMSC_BOOST_MSVC, < 1310 )
# define UVMSC_BOOST_EXCEPTION_DISABLE
#endif

#if !defined( UVMSC_BOOST_EXCEPTION_DISABLE )
# include <packages/boost/include/exception/exception.hpp>
# include <packages/boost/include/current_function.hpp>
# define UVMSC_BOOST_THROW_EXCEPTION(x) ::uvmsc_boost::exception_detail::throw_exception_(x,UVMSC_BOOST_CURRENT_FUNCTION,__FILE__,__LINE__)
#else
# define UVMSC_BOOST_THROW_EXCEPTION(x) ::uvmsc_boost::throw_exception(x)
#endif

namespace uvmsc_boost
{
#ifdef UVMSC_BOOST_NO_EXCEPTIONS

void throw_exception( std::exception const & e ); // user defined

#else

inline void throw_exception_assert_compatibility( std::exception const & ) { }

template<class E> UVMSC_BOOST_ATTRIBUTE_NORETURN inline void throw_exception( E const & e )
{
    //All boost exceptions are required to derive from std::exception,
    //to ensure compatibility with UVMSC_BOOST_NO_EXCEPTIONS.
    throw_exception_assert_compatibility(e);

#ifndef UVMSC_BOOST_EXCEPTION_DISABLE
    throw enable_current_exception(enable_error_info(e));
#else
    throw e;
#endif
}

#endif

#if !defined( UVMSC_BOOST_EXCEPTION_DISABLE )
    namespace
    exception_detail
    {
        template <class E>
        UVMSC_BOOST_ATTRIBUTE_NORETURN
        void
        throw_exception_( E const & x, char const * current_function, char const * file, int line )
        {
            uvmsc_boost::throw_exception(
                set_info(
                    set_info(
                        set_info(
                            uvmsc_boost::enable_error_info(x),
                            throw_function(current_function)),
                        throw_file(file)),
                    throw_line(line)));
        }
    }
#endif
} // namespace uvmsc_boost

#endif // #ifndef UVMSC_BOOST_THROW_EXCEPTION_HPP_INCLUDED
