/*
 *
 * Copyright (c) 2002
 * John Maddock
 *
 * Use, modification and distribution are subject to the
 * Boost Software License, Version 1.0. (See accompanying file
 * LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
 *
 */

 /*
  *   LOCATION:    see http://www.boost.org for most recent version.
  *   FILE         char_regex_traits.cpp
  *   VERSION      see <packages/boost/include/version.hpp>
  *   DESCRIPTION: Declares deprecated traits classes char_regex_traits<>.
  */


#ifndef UVMSC_BOOST_REGEX_V4_CHAR_REGEX_TRAITS_HPP
#define UVMSC_BOOST_REGEX_V4_CHAR_REGEX_TRAITS_HPP

#ifdef UVMSC_BOOST_MSVC
#pragma warning(push)
#pragma warning(disable: 4103)
#endif
#ifdef UVMSC_BOOST_HAS_ABI_HEADERS
#  include UVMSC_BOOST_ABI_PREFIX
#endif
#ifdef UVMSC_BOOST_MSVC
#pragma warning(pop)
#endif

namespace uvmsc_boost{

namespace deprecated{
//
// class char_regex_traits_i
// provides case insensitive traits classes (deprecated):
template <class charT>
class char_regex_traits_i : public regex_traits<charT> {};

template<>
class char_regex_traits_i<char> : public regex_traits<char>
{
public:
   typedef char char_type;
   typedef unsigned char uchar_type;
   typedef unsigned int size_type;
   typedef regex_traits<char> base_type;

};

#ifndef UVMSC_BOOST_NO_WREGEX
template<>
class char_regex_traits_i<wchar_t> : public regex_traits<wchar_t>
{
public:
   typedef wchar_t char_type;
   typedef unsigned short uchar_type;
   typedef unsigned int size_type;
   typedef regex_traits<wchar_t> base_type;

};
#endif
} // namespace deprecated
} // namespace uvmsc_boost

#ifdef UVMSC_BOOST_MSVC
#pragma warning(push)
#pragma warning(disable: 4103)
#endif
#ifdef UVMSC_BOOST_HAS_ABI_HEADERS
#  include UVMSC_BOOST_ABI_SUFFIX
#endif
#ifdef UVMSC_BOOST_MSVC
#pragma warning(pop)
#endif

#endif // include

