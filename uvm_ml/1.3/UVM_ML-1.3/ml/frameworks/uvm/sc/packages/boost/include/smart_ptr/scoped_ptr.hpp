#ifndef UVMSC_BOOST_SMART_PTR_SCOPED_PTR_HPP_INCLUDED
#define UVMSC_BOOST_SMART_PTR_SCOPED_PTR_HPP_INCLUDED

//  (C) Copyright Greg Colvin and Beman Dawes 1998, 1999.
//  Copyright (c) 2001, 2002 Peter Dimov
//
//  Distributed under the Boost Software License, Version 1.0. (See
//  accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt)
//
//  http://www.boost.org/libs/smart_ptr/scoped_ptr.htm
//

#include <packages/boost/include/assert.hpp>
#include <packages/boost/include/checked_delete.hpp>
#include <packages/boost/include/detail/workaround.hpp>

#ifndef UVMSC_BOOST_NO_AUTO_PTR
# include <memory>          // for std::auto_ptr
#endif

namespace uvmsc_boost
{

// Debug hooks

#if defined(UVMSC_BOOST_SP_ENABLE_DEBUG_HOOKS)

void sp_scalar_constructor_hook(void * p);
void sp_scalar_destructor_hook(void * p);

#endif

//  scoped_ptr mimics a built-in pointer except that it guarantees deletion
//  of the object pointed to, either on destruction of the scoped_ptr or via
//  an explicit reset(). scoped_ptr is a simple solution for simple needs;
//  use shared_ptr or std::auto_ptr if your needs are more complex.

template<class T> class scoped_ptr // noncopyable
{
private:

    T * px;

    scoped_ptr(scoped_ptr const &);
    scoped_ptr & operator=(scoped_ptr const &);

    typedef scoped_ptr<T> this_type;

    void operator==( scoped_ptr const& ) const;
    void operator!=( scoped_ptr const& ) const;

public:

    typedef T element_type;

    explicit scoped_ptr( T * p = 0 ): px( p ) // never throws
    {
#if defined(UVMSC_BOOST_SP_ENABLE_DEBUG_HOOKS)
        uvmsc_boost::sp_scalar_constructor_hook( px );
#endif
    }

#ifndef UVMSC_BOOST_NO_AUTO_PTR

    explicit scoped_ptr( std::auto_ptr<T> p ): px( p.release() ) // never throws
    {
#if defined(UVMSC_BOOST_SP_ENABLE_DEBUG_HOOKS)
        uvmsc_boost::sp_scalar_constructor_hook( px );
#endif
    }

#endif

    ~scoped_ptr() // never throws
    {
#if defined(UVMSC_BOOST_SP_ENABLE_DEBUG_HOOKS)
        uvmsc_boost::sp_scalar_destructor_hook( px );
#endif
        uvmsc_boost::checked_delete( px );
    }

    void reset(T * p = 0) // never throws
    {
        UVMSC_BOOST_ASSERT( p == 0 || p != px ); // catch self-reset errors
        this_type(p).swap(*this);
    }

    T & operator*() const // never throws
    {
        UVMSC_BOOST_ASSERT( px != 0 );
        return *px;
    }

    T * operator->() const // never throws
    {
        UVMSC_BOOST_ASSERT( px != 0 );
        return px;
    }

    T * get() const // never throws
    {
        return px;
    }

// implicit conversion to "bool"
#include <packages/boost/include/smart_ptr/detail/operator_bool.hpp>

    void swap(scoped_ptr & b) // never throws
    {
        T * tmp = b.px;
        b.px = px;
        px = tmp;
    }
};

template<class T> inline void swap(scoped_ptr<T> & a, scoped_ptr<T> & b) // never throws
{
    a.swap(b);
}

// get_pointer(p) is a generic way to say p.get()

template<class T> inline T * get_pointer(scoped_ptr<T> const & p)
{
    return p.get();
}

} // namespace uvmsc_boost

#endif // #ifndef UVMSC_BOOST_SMART_PTR_SCOPED_PTR_HPP_INCLUDED
