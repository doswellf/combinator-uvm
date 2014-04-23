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
  *   FILE         instances.cpp
  *   VERSION      see <packages/boost/include/version.hpp>
  *   DESCRIPTION: Defines those template instances that are placed in the
  *                library rather than in the users object files.
  */

//
// note no include guard, we may include this multiple times:
//
#ifndef UVMSC_BOOST_REGEX_NO_EXTERNAL_TEMPLATES

namespace uvmsc_boost{

//
// this header can be included multiple times, each time with
// a different character type, UVMSC_BOOST_REGEX_CHAR_T must be defined
// first:
//
#ifndef UVMSC_BOOST_REGEX_CHAR_T
#  error "UVMSC_BOOST_REGEX_CHAR_T not defined"
#endif

#ifndef UVMSC_BOOST_REGEX_TRAITS_T
#  define UVMSC_BOOST_REGEX_TRAITS_T , uvmsc_boost::regex_traits<UVMSC_BOOST_REGEX_CHAR_T >
#endif

//
// what follows is compiler specific:
//

#if  defined(__BORLANDC__) && (__BORLANDC__ < 0x600)

#ifdef UVMSC_BOOST_HAS_ABI_HEADERS
#  include UVMSC_BOOST_ABI_PREFIX
#endif

#  ifndef UVMSC_BOOST_REGEX_INSTANTIATE
#     pragma option push -Jgx
#  endif

template class UVMSC_BOOST_REGEX_DECL basic_regex< UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >;
template class UVMSC_BOOST_REGEX_DECL match_results< const UVMSC_BOOST_REGEX_CHAR_T* >;
#ifndef UVMSC_BOOST_NO_STD_ALLOCATOR
template class UVMSC_BOOST_REGEX_DECL ::uvmsc_boost::re_detail::perl_matcher<UVMSC_BOOST_REGEX_CHAR_T const *, match_results< const UVMSC_BOOST_REGEX_CHAR_T* >::allocator_type UVMSC_BOOST_REGEX_TRAITS_T >;
#endif

#  ifndef UVMSC_BOOST_REGEX_INSTANTIATE
#     pragma option pop
#  endif

#ifdef UVMSC_BOOST_HAS_ABI_HEADERS
#  include UVMSC_BOOST_ABI_SUFFIX
#endif

#elif defined(UVMSC_BOOST_MSVC) || defined(__ICL)

#  ifndef UVMSC_BOOST_REGEX_INSTANTIATE
#     ifdef __GNUC__
#        define template __extension__ extern template
#     else
#        if UVMSC_BOOST_MSVC > 1310
#           define UVMSC_BOOST_REGEX_TEMPLATE_DECL
#        endif
#        define template extern template
#     endif
#  endif

#ifndef UVMSC_BOOST_REGEX_TEMPLATE_DECL
#  define UVMSC_BOOST_REGEX_TEMPLATE_DECL UVMSC_BOOST_REGEX_DECL
#endif

#  ifdef UVMSC_BOOST_MSVC
#     pragma warning(push)
#     pragma warning(disable : 4251 4231 4660)
#  endif

template class UVMSC_BOOST_REGEX_TEMPLATE_DECL basic_regex< UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >;

#if !UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, < 1300)
template class UVMSC_BOOST_REGEX_TEMPLATE_DECL match_results< const UVMSC_BOOST_REGEX_CHAR_T* >;
#endif
#ifndef UVMSC_BOOST_NO_STD_ALLOCATOR
template class UVMSC_BOOST_REGEX_TEMPLATE_DECL ::uvmsc_boost::re_detail::perl_matcher<UVMSC_BOOST_REGEX_CHAR_T const *, match_results< const UVMSC_BOOST_REGEX_CHAR_T* >::allocator_type UVMSC_BOOST_REGEX_TRAITS_T >;
#endif
#if !(defined(UVMSC_BOOST_DINKUMWARE_STDLIB) && (UVMSC_BOOST_DINKUMWARE_STDLIB <= 1))\
   && !(defined(UVMSC_BOOST_INTEL_CXX_VERSION) && (UVMSC_BOOST_INTEL_CXX_VERSION <= 800))\
   && !(defined(__SGI_STL_PORT) || defined(_STLPORT_VERSION))\
   && !defined(UVMSC_BOOST_REGEX_ICU_INSTANCES)
#if !UVMSC_BOOST_WORKAROUND(UVMSC_BOOST_MSVC, < 1300)
template class UVMSC_BOOST_REGEX_TEMPLATE_DECL match_results< std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator >;
#endif
#ifndef UVMSC_BOOST_NO_STD_ALLOCATOR
template class UVMSC_BOOST_REGEX_TEMPLATE_DECL ::uvmsc_boost::re_detail::perl_matcher< std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator, match_results< std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator >::allocator_type, uvmsc_boost::regex_traits<UVMSC_BOOST_REGEX_CHAR_T > >;
#endif
#endif


#  ifdef UVMSC_BOOST_MSVC
#     pragma warning(pop)
#  endif

#  ifdef template
#     undef template
#  endif

#undef UVMSC_BOOST_REGEX_TEMPLATE_DECL

#elif (defined(__GNUC__) && (__GNUC__ >= 3)) || !defined(UVMSC_BOOST_NO_EXTERN_TEMPLATE)

#  ifndef UVMSC_BOOST_REGEX_INSTANTIATE
#     ifdef __GNUC__
#        define template __extension__ extern template
#     else
#        define template extern template
#     endif
#  endif

#if !defined(UVMSC_BOOST_NO_STD_LOCALE) && !defined(UVMSC_BOOST_REGEX_ICU_INSTANCES)
namespace re_detail{
template UVMSC_BOOST_REGEX_DECL
std::locale cpp_regex_traits_base<UVMSC_BOOST_REGEX_CHAR_T>::imbue(const std::locale& l);

template UVMSC_BOOST_REGEX_DECL
cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::string_type 
   cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::transform_primary(const UVMSC_BOOST_REGEX_CHAR_T* p1, const UVMSC_BOOST_REGEX_CHAR_T* p2) const;
template UVMSC_BOOST_REGEX_DECL
cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::string_type 
   cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::transform(const UVMSC_BOOST_REGEX_CHAR_T* p1, const UVMSC_BOOST_REGEX_CHAR_T* p2) const;
template UVMSC_BOOST_REGEX_DECL
cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::string_type 
   cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::lookup_collatename(const UVMSC_BOOST_REGEX_CHAR_T* p1, const UVMSC_BOOST_REGEX_CHAR_T* p2) const;
template UVMSC_BOOST_REGEX_DECL
void cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::init();
template UVMSC_BOOST_REGEX_DECL
cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::char_class_type 
   cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::lookup_classname_imp(const UVMSC_BOOST_REGEX_CHAR_T* p1, const UVMSC_BOOST_REGEX_CHAR_T* p2) const;
#ifdef UVMSC_BOOST_REGEX_BUGGY_CTYPE_FACET
template UVMSC_BOOST_REGEX_DECL
bool cpp_regex_traits_implementation<UVMSC_BOOST_REGEX_CHAR_T>::isctype(const UVMSC_BOOST_REGEX_CHAR_T c, char_class_type mask) const;
#endif
} // namespace
template UVMSC_BOOST_REGEX_DECL
int cpp_regex_traits<UVMSC_BOOST_REGEX_CHAR_T>::toi(const UVMSC_BOOST_REGEX_CHAR_T*& first, const UVMSC_BOOST_REGEX_CHAR_T* last, int radix)const;
template UVMSC_BOOST_REGEX_DECL
std::string cpp_regex_traits<UVMSC_BOOST_REGEX_CHAR_T>::catalog_name(const std::string& name);
template UVMSC_BOOST_REGEX_DECL
std::string& cpp_regex_traits<UVMSC_BOOST_REGEX_CHAR_T>::get_catalog_name_inst();
template UVMSC_BOOST_REGEX_DECL
std::string cpp_regex_traits<UVMSC_BOOST_REGEX_CHAR_T>::get_catalog_name();
#ifdef UVMSC_BOOST_HAS_THREADS
template UVMSC_BOOST_REGEX_DECL
static_mutex& cpp_regex_traits<UVMSC_BOOST_REGEX_CHAR_T>::get_mutex_inst();
#endif
#endif

template UVMSC_BOOST_REGEX_DECL basic_regex<UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >& 
   basic_regex<UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >::do_assign(
      const UVMSC_BOOST_REGEX_CHAR_T* p1, 
      const UVMSC_BOOST_REGEX_CHAR_T* p2, 
      flag_type f);
template UVMSC_BOOST_REGEX_DECL basic_regex<UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >::locale_type UVMSC_BOOST_REGEX_CALL 
   basic_regex<UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >::imbue(locale_type l);

template UVMSC_BOOST_REGEX_DECL void UVMSC_BOOST_REGEX_CALL 
   match_results<const UVMSC_BOOST_REGEX_CHAR_T*>::maybe_assign(
      const match_results<const UVMSC_BOOST_REGEX_CHAR_T*>& m);

namespace re_detail{
template UVMSC_BOOST_REGEX_DECL void perl_matcher<UVMSC_BOOST_REGEX_CHAR_T const *, match_results< const UVMSC_BOOST_REGEX_CHAR_T* >::allocator_type UVMSC_BOOST_REGEX_TRAITS_T >::construct_init(
      const basic_regex<UVMSC_BOOST_REGEX_CHAR_T UVMSC_BOOST_REGEX_TRAITS_T >& e, match_flag_type f);
template UVMSC_BOOST_REGEX_DECL bool perl_matcher<UVMSC_BOOST_REGEX_CHAR_T const *, match_results< const UVMSC_BOOST_REGEX_CHAR_T* >::allocator_type UVMSC_BOOST_REGEX_TRAITS_T >::match();
template UVMSC_BOOST_REGEX_DECL bool perl_matcher<UVMSC_BOOST_REGEX_CHAR_T const *, match_results< const UVMSC_BOOST_REGEX_CHAR_T* >::allocator_type UVMSC_BOOST_REGEX_TRAITS_T >::find();
} // namespace

#if (defined(__GLIBCPP__) || defined(__GLIBCXX__)) \
   && !defined(UVMSC_BOOST_REGEX_ICU_INSTANCES)\
   && !defined(__SGI_STL_PORT)\
   && !defined(_STLPORT_VERSION)
// std:basic_string<>::const_iterator instances as well:
template UVMSC_BOOST_REGEX_DECL void UVMSC_BOOST_REGEX_CALL 
   match_results<std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator>::maybe_assign(
      const match_results<std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator>& m);

namespace re_detail{
template UVMSC_BOOST_REGEX_DECL void perl_matcher<std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator, match_results< std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator >::allocator_type, uvmsc_boost::regex_traits<UVMSC_BOOST_REGEX_CHAR_T > >::construct_init(
      const basic_regex<UVMSC_BOOST_REGEX_CHAR_T>& e, match_flag_type f);
template UVMSC_BOOST_REGEX_DECL bool perl_matcher<std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator, match_results< std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator >::allocator_type, uvmsc_boost::regex_traits<UVMSC_BOOST_REGEX_CHAR_T > >::match();
template UVMSC_BOOST_REGEX_DECL bool perl_matcher<std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator, match_results< std::basic_string<UVMSC_BOOST_REGEX_CHAR_T>::const_iterator >::allocator_type, uvmsc_boost::regex_traits<UVMSC_BOOST_REGEX_CHAR_T > >::find();
} // namespace
#endif

#  ifdef template
#     undef template
#  endif


#endif

} // namespace uvmsc_boost

#endif // UVMSC_BOOST_REGEX_NO_EXTERNAL_TEMPLATES





