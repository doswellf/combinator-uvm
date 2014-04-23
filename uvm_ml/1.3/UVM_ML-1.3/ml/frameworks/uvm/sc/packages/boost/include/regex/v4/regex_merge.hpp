/*
 *
 * Copyright (c) 1998-2002
 * John Maddock
 *
 * Use, modification and distribution are subject to the 
 * Boost Software License, Version 1.0. (See accompanying file 
 * LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
 *
 */

 /*
  *   LOCATION:    see http://www.boost.org for most recent version.
  *   FILE         regex_format.hpp
  *   VERSION      see <packages/boost/include/version.hpp>
  *   DESCRIPTION: Provides formatting output routines for search and replace
  *                operations.  Note this is an internal header file included
  *                by regex.hpp, do not include on its own.
  */

#ifndef UVMSC_BOOST_REGEX_V4_REGEX_MERGE_HPP
#define UVMSC_BOOST_REGEX_V4_REGEX_MERGE_HPP


namespace uvmsc_boost{

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

template <class OutputIterator, class Iterator, class traits, class charT>
inline OutputIterator regex_merge(OutputIterator out,
                         Iterator first,
                         Iterator last,
                         const basic_regex<charT, traits>& e, 
                         const charT* fmt, 
                         match_flag_type flags = match_default)
{
   return regex_replace(out, first, last, e, fmt, flags);
}

template <class OutputIterator, class Iterator, class traits, class charT>
inline OutputIterator regex_merge(OutputIterator out,
                         Iterator first,
                         Iterator last,
                         const basic_regex<charT, traits>& e, 
                         const std::basic_string<charT>& fmt,
                         match_flag_type flags = match_default)
{
   return regex_merge(out, first, last, e, fmt.c_str(), flags);
}

template <class traits, class charT>
inline std::basic_string<charT> regex_merge(const std::basic_string<charT>& s,
                         const basic_regex<charT, traits>& e, 
                         const charT* fmt,
                         match_flag_type flags = match_default)
{
   return regex_replace(s, e, fmt, flags);
}

template <class traits, class charT>
inline std::basic_string<charT> regex_merge(const std::basic_string<charT>& s,
                         const basic_regex<charT, traits>& e, 
                         const std::basic_string<charT>& fmt,
                         match_flag_type flags = match_default)
{
   return regex_replace(s, e, fmt, flags);
}

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

} // namespace uvmsc_boost

#endif  // UVMSC_BOOST_REGEX_V4_REGEX_MERGE_HPP


