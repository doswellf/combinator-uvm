# copyright John Maddock 2006-7
# Distributed under the Boost Software License, Version 1.0. 
# (See accompanying file LICENSE_1_0.txt or copy at 
# http://www.boost.org/LICENSE_1_0.txt.
#
# auto generated makefile for gcc compiler
#
# usage:
# make
#   brings libraries up to date
# make clean
#   deletes temporary object files (but not archives).
#

#
# the following environment variables are recognised:
# ICU_PATH= Path to ICU installation.
# CXXFLAGS= extra compiler options - note applies to all build variants
# INCLUDES= additional include directories
# LDFLAGS=  additional linker options
# LIBS=     additional library files

# compiler:
CXX = $(UVM_ML_CC)
LINKER ?= $(UVM_ML_LD) -shared

#
# compiler options for release build:
#
C1=-c -O2 -I../../.. $(BIT_CXXFLAGS) -I../../../../..
#
# compiler options for debug build:
#
C2=-c -g -I../../.. $(BIT_CXXFLAGS) -I../../../../..

ifeq "$(ICU_PATH)" ""
$(warning "Building Boost.Regex without ICU / Unicode support:")
$(warning "Hint: set ICU_PATH on the nmake command line to point ")
$(warning "to your ICU installation if you have one.")
else
ICU_CXXFLAGS= -DBOOST_HAS_ICU=1 -I$(ICU_PATH)/include
ICU_LDFLAGS= -L$(ICU_PATH)/lib
ICU_LIBS= -licui18n -licuuc
$(warning "Building Boost.Regex with ICU in $(ICU_PATH)")
endif


OBJEXT ?= o
LIB_DIR ?= .
LIB_NAME ?= libboost_regex-gcc-1_47.${UVM_ML_COMPILER_VERSION}.so


ALL_HEADER= ../../../include/regex/config.hpp \
			../../../include/regex/icu.hpp \
			../../../include/regex/pattern_except.hpp \
			../../../include/regex/regex_traits.hpp \
			../../../include/regex/user.hpp \
			../../../include/regex/v4/basic_regex.hpp \
			../../../include/regex/v4/basic_regex_creator.hpp \
			../../../include/regex/v4/basic_regex_parser.hpp \
			../../../include/regex/v4/c_regex_traits.hpp \
			../../../include/regex/v4/char_regex_traits.hpp \
			../../../include/regex/v4/cpp_regex_traits.hpp \
			../../../include/regex/v4/cregex.hpp \
			../../../include/regex/v4/error_type.hpp \
			../../../include/regex/v4/fileiter.hpp \
			../../../include/regex/v4/instances.hpp \
			../../../include/regex/v4/iterator_category.hpp \
			../../../include/regex/v4/iterator_traits.hpp \
			../../../include/regex/v4/match_flags.hpp \
			../../../include/regex/v4/match_results.hpp \
			../../../include/regex/v4/mem_block_cache.hpp \
			../../../include/regex/v4/perl_matcher.hpp \
			../../../include/regex/v4/perl_matcher_common.hpp \
			../../../include/regex/v4/perl_matcher_non_recursive.hpp \
			../../../include/regex/v4/perl_matcher_recursive.hpp \
			../../../include/regex/v4/primary_transform.hpp \
			../../../include/regex/v4/protected_call.hpp \
			../../../include/regex/v4/regbase.hpp \
			../../../include/regex/v4/regex.hpp \
			../../../include/regex/v4/regex_format.hpp \
			../../../include/regex/v4/regex_fwd.hpp \
			../../../include/regex/v4/regex_grep.hpp \
			../../../include/regex/v4/regex_iterator.hpp \
			../../../include/regex/v4/regex_match.hpp \
			../../../include/regex/v4/regex_merge.hpp \
			../../../include/regex/v4/regex_raw_buffer.hpp \
			../../../include/regex/v4/regex_replace.hpp \
			../../../include/regex/v4/regex_search.hpp \
			../../../include/regex/v4/regex_split.hpp \
			../../../include/regex/v4/regex_token_iterator.hpp \
			../../../include/regex/v4/regex_traits.hpp \
			../../../include/regex/v4/regex_traits_defaults.hpp \
			../../../include/regex/v4/regex_workaround.hpp \
			../../../include/regex/v4/states.hpp \
			../../../include/regex/v4/sub_match.hpp \
			../../../include/regex/v4/syntax_type.hpp \
			../../../include/regex/v4/u32regex_iterator.hpp \
			../../../include/regex/v4/u32regex_token_iterator.hpp \
			../../../include/regex/v4/w32_regex_traits.hpp \
			../../../include/regex/config/borland.hpp \
			../../../include/regex/config/cwchar.hpp

all : boost_regex-gcc-1_47_shared  lns

clean :  boost_regex-gcc-1_47_clean boost_regex-gcc-d-1_47_clean 
	-rm *.so

install : all

lns: $(LIB_NAME)
	mkdir -p $(LIB_DIR)
	ln -sf $(CURDIR)/$(LIB_NAME) $(LIB_DIR)/libuvmscboost_regex.so

########################################################
#
# section for libboost_regex-gcc-1_47.a
#
########################################################
boost_regex-gcc-1_47_shared/c_regex_traits.$(OBJEXT): ../src/c_regex_traits.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/c_regex_traits.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/c_regex_traits.cpp

boost_regex-gcc-1_47_shared/cpp_regex_traits.$(OBJEXT): ../src/cpp_regex_traits.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/cpp_regex_traits.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/cpp_regex_traits.cpp

boost_regex-gcc-1_47_shared/cregex.$(OBJEXT): ../src/cregex.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/cregex.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/cregex.cpp

boost_regex-gcc-1_47_shared/fileiter.$(OBJEXT): ../src/fileiter.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/fileiter.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/fileiter.cpp

boost_regex-gcc-1_47_shared/icu.$(OBJEXT): ../src/icu.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/icu.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/icu.cpp

boost_regex-gcc-1_47_shared/instances.$(OBJEXT): ../src/instances.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/instances.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/instances.cpp

boost_regex-gcc-1_47_shared/posix_api.$(OBJEXT): ../src/posix_api.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/posix_api.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/posix_api.cpp

boost_regex-gcc-1_47_shared/regex.$(OBJEXT): ../src/regex.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/regex.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/regex.cpp

boost_regex-gcc-1_47_shared/regex_debug.$(OBJEXT): ../src/regex_debug.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/regex_debug.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/regex_debug.cpp

boost_regex-gcc-1_47_shared/regex_raw_buffer.$(OBJEXT): ../src/regex_raw_buffer.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/regex_raw_buffer.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/regex_raw_buffer.cpp

boost_regex-gcc-1_47_shared/regex_traits_defaults.$(OBJEXT): ../src/regex_traits_defaults.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/regex_traits_defaults.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/regex_traits_defaults.cpp

boost_regex-gcc-1_47_shared/static_mutex.$(OBJEXT): ../src/static_mutex.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/static_mutex.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/static_mutex.cpp

boost_regex-gcc-1_47_shared/usinstances.$(OBJEXT): ../src/usinstances.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/usinstances.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/usinstances.cpp

boost_regex-gcc-1_47_shared/w32_regex_traits.$(OBJEXT): ../src/w32_regex_traits.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/w32_regex_traits.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/w32_regex_traits.cpp

boost_regex-gcc-1_47_shared/wc_regex_traits.$(OBJEXT): ../src/wc_regex_traits.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/wc_regex_traits.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/wc_regex_traits.cpp

boost_regex-gcc-1_47_shared/wide_posix_api.$(OBJEXT): ../src/wide_posix_api.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/wide_posix_api.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/wide_posix_api.cpp

boost_regex-gcc-1_47_shared/winstances.$(OBJEXT): ../src/winstances.cpp $(ALL_HEADER)
	$(CXX) $(INCLUDES) -o boost_regex-gcc-1_47_shared/winstances.$(OBJEXT) $(C1) $(CXXFLAGS) $(ICU_CXXFLAGS) ../src/winstances.cpp

boost_regex-gcc-1_47_shared : 
	mkdir -p boost_regex-gcc-1_47_shared

boost_regex-gcc-1_47_clean :
	rm -rf boost_regex-gcc-1_47_shared

$(LIB_NAME) : boost_regex-gcc-1_47_shared/c_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/cpp_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/cregex.$(OBJEXT) boost_regex-gcc-1_47_shared/fileiter.$(OBJEXT) boost_regex-gcc-1_47_shared/icu.$(OBJEXT) boost_regex-gcc-1_47_shared/instances.$(OBJEXT) boost_regex-gcc-1_47_shared/posix_api.$(OBJEXT) boost_regex-gcc-1_47_shared/regex.$(OBJEXT) boost_regex-gcc-1_47_shared/regex_debug.$(OBJEXT) boost_regex-gcc-1_47_shared/regex_raw_buffer.$(OBJEXT) boost_regex-gcc-1_47_shared/regex_traits_defaults.$(OBJEXT) boost_regex-gcc-1_47_shared/static_mutex.$(OBJEXT) boost_regex-gcc-1_47_shared/usinstances.$(OBJEXT) boost_regex-gcc-1_47_shared/w32_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/wc_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/wide_posix_api.$(OBJEXT) boost_regex-gcc-1_47_shared/winstances.$(OBJEXT)
	$(LINKER) -o $@ $(LDFLAGS)  $(ICU_LDFLAGS)  boost_regex-gcc-1_47_shared/c_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/cpp_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/cregex.$(OBJEXT) boost_regex-gcc-1_47_shared/fileiter.$(OBJEXT) boost_regex-gcc-1_47_shared/icu.$(OBJEXT) boost_regex-gcc-1_47_shared/instances.$(OBJEXT) boost_regex-gcc-1_47_shared/posix_api.$(OBJEXT) boost_regex-gcc-1_47_shared/regex.$(OBJEXT) boost_regex-gcc-1_47_shared/regex_debug.$(OBJEXT) boost_regex-gcc-1_47_shared/regex_raw_buffer.$(OBJEXT) boost_regex-gcc-1_47_shared/regex_traits_defaults.$(OBJEXT) boost_regex-gcc-1_47_shared/static_mutex.$(OBJEXT) boost_regex-gcc-1_47_shared/usinstances.$(OBJEXT) boost_regex-gcc-1_47_shared/w32_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/wc_regex_traits.$(OBJEXT) boost_regex-gcc-1_47_shared/wide_posix_api.$(OBJEXT) boost_regex-gcc-1_47_shared/winstances.$(OBJEXT) $(ICU_LIBS) $(LIBS)

