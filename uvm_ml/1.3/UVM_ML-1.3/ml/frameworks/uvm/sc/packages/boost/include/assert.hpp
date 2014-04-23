//
//  packages/boost/include/assert.hpp - UVMSC_BOOST_ASSERT(expr)
//                     UVMSC_BOOST_ASSERT_MSG(expr, msg)
//                     UVMSC_BOOST_VERIFY(expr)
//
//  Copyright (c) 2001, 2002 Peter Dimov and Multi Media Ltd.
//  Copyright (c) 2007 Peter Dimov
//  Copyright (c) Beman Dawes 2011
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
//  Note: There are no include guards. This is intentional.
//
//  See http://www.boost.org/libs/utility/assert.html for documentation.
//

//
// Stop inspect complaining about use of 'assert':
//
// boostinspect:naassert_macro
//

//--------------------------------------------------------------------------------------//
//                                     UVMSC_BOOST_ASSERT                                     //
//--------------------------------------------------------------------------------------//

#undef UVMSC_BOOST_ASSERT

#if defined(UVMSC_BOOST_DISABLE_ASSERTS)

# define UVMSC_BOOST_ASSERT(expr) ((void)0)

#elif defined(UVMSC_BOOST_ENABLE_ASSERT_HANDLER)

#include <packages/boost/include/current_function.hpp>

namespace uvmsc_boost
{
  void assertion_failed(char const * expr,
                        char const * function, char const * file, long line); // user defined
} // namespace uvmsc_boost

#define UVMSC_BOOST_ASSERT(expr) ((expr) \
  ? ((void)0) \
  : ::uvmsc_boost::assertion_failed(#expr, UVMSC_BOOST_CURRENT_FUNCTION, __FILE__, __LINE__))

#else
# include <assert.h> // .h to support old libraries w/o <cassert> - effect is the same
# define UVMSC_BOOST_ASSERT(expr) assert(expr)
#endif

//--------------------------------------------------------------------------------------//
//                                   UVMSC_BOOST_ASSERT_MSG                                   //
//--------------------------------------------------------------------------------------//

# undef UVMSC_BOOST_ASSERT_MSG

#if defined(UVMSC_BOOST_DISABLE_ASSERTS) || defined(NDEBUG)

  #define UVMSC_BOOST_ASSERT_MSG(expr, msg) ((void)0)

#elif defined(UVMSC_BOOST_ENABLE_ASSERT_HANDLER)

  #include <packages/boost/include/current_function.hpp>

  namespace uvmsc_boost
  {
    void assertion_failed_msg(char const * expr, char const * msg,
                              char const * function, char const * file, long line); // user defined
  } // namespace uvmsc_boost

  #define UVMSC_BOOST_ASSERT_MSG(expr, msg) ((expr) \
    ? ((void)0) \
    : ::uvmsc_boost::assertion_failed_msg(#expr, msg, UVMSC_BOOST_CURRENT_FUNCTION, __FILE__, __LINE__))

#else
  #ifndef UVMSC_BOOST_ASSERT_HPP
    #define UVMSC_BOOST_ASSERT_HPP
    #include <cstdlib>
    #include <iostream>
    #include <packages/boost/include/current_function.hpp>

    //  IDE's like Visual Studio perform better if output goes to std::cout or
    //  some other stream, so allow user to configure output stream:
    #ifndef UVMSC_BOOST_ASSERT_MSG_OSTREAM
    # define UVMSC_BOOST_ASSERT_MSG_OSTREAM std::cerr
    #endif

    namespace uvmsc_boost
    { 
      namespace assertion 
      { 
        namespace detail
        {
          inline void assertion_failed_msg(char const * expr, char const * msg, char const * function,
            char const * file, long line)
          {
            UVMSC_BOOST_ASSERT_MSG_OSTREAM
              << "***** Internal Program Error - assertion (" << expr << ") failed in "
              << function << ":\n"
              << file << '(' << line << "): " << msg << std::endl;
            std::abort();
          }
        } // detail
      } // assertion
    } // detail
  #endif

  #define UVMSC_BOOST_ASSERT_MSG(expr, msg) ((expr) \
    ? ((void)0) \
    : ::uvmsc_boost::assertion::detail::assertion_failed_msg(#expr, msg, \
          UVMSC_BOOST_CURRENT_FUNCTION, __FILE__, __LINE__))
#endif

//--------------------------------------------------------------------------------------//
//                                     UVMSC_BOOST_VERIFY                                     //
//--------------------------------------------------------------------------------------//

#undef UVMSC_BOOST_VERIFY

#if defined(UVMSC_BOOST_DISABLE_ASSERTS) || ( !defined(UVMSC_BOOST_ENABLE_ASSERT_HANDLER) && defined(NDEBUG) )

# define UVMSC_BOOST_VERIFY(expr) ((void)(expr))

#else

# define UVMSC_BOOST_VERIFY(expr) UVMSC_BOOST_ASSERT(expr)

#endif
