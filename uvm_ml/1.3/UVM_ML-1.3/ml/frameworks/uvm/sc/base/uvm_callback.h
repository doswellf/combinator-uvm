//----------------------------------------------------------------------
//   Copyright 2012 Advanced Micro Devices Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

/*! \file uvm_callback.h
  \brief Header file for uvm_callback.
*/
#ifndef __UVM_CALLBACK_AGENT_H__
#define __UVM_CALLBACK_AGENT_H__

#include <algorithm>

namespace uvm {

class uvm_callback; 
class uvm_callback_by_priority; 
typedef uvm_callback* p_uvm_callback;       // Pointer to Callback
typedef std::vector<p_uvm_callback> uvm_callback_ptr_vector;
typedef uvm_callback_ptr_vector* uvm_callback_ptr_vector_ptr;

//------------------------------------------------------------------------------
// Class: uvm_callback
//   Virtual Base of Prioritized uvm_callback
//------------------------------------------------------------------------------
/*! \class uvm_callback
  \brief Virtual Base of Prioritized uvm_callback.

  
*/
class uvm_callback
{
    friend class uvm_callback_agent;

protected:
    // Constructor: uvm_callback
    uvm_callback ( int priority ) :
        _priority ( priority ) { };  

    // Desstructor: uvm_callback
    virtual ~uvm_callback ( ) { };    

    // Function: call
    virtual void call ( ) = 0;

public:
    // Function: priority
    // Returns:
    //  Priority needed for sorting
    unsigned int priority ( ) const { return _priority; }                

protected:
    unsigned int _priority; 
}; 

//------------------------------------------------------------------------------
// Class: function_callback
//   Template class used for attaching prioritized callback function pointers 
//------------------------------------------------------------------------------
/*! \class function_callback
  \brief Template class used for attaching prioritized callback function pointers.

  
*/
template <typename t_return, 
	      typename t_arg1> 
class function_callback : public uvm_callback
{
friend class uvm_callback_agent;
protected:
    // Constructor: function_callback
    // Parameters:
    //  p_return - function callback return value
    //  p_func   - function pointer to callback function
    //  arg1     - argument of callback function
    //  priority - priority of callback (0 - lowest priority)
    function_callback ( t_return* p_return , t_return (*p_func)(t_arg1) , t_arg1 arg1 , unsigned int priority = 0 ):
        uvm_callback(priority),
        _p_return(p_return),
        _p_func(p_func),
        _arg1(arg1) 
    { }; 

    // Destructor: function_callback
    virtual ~function_callback ( ) { };

    // Function: call
    //  Call function callback.
    void call ( ) 
    { 
        if ( _p_return ) 
            *_p_return = (* _p_func) ( _arg1 ); 
        else 
            (* _p_func) ( _arg1 ); 
    }
protected:
    t_return* _p_return; 
    t_return (*_p_func)(t_arg1); 
    t_arg1   _arg1; 
}; 


//------------------------------------------------------------------------------
// Class: void_function_callback
///  Template class used for attaching prioritized callback function pointers 
//------------------------------------------------------------------------------
/*! \class void_function_callback
  \brief Template class used for attaching prioritized callback function pointers.

  
*/
template <typename t_arg1> 
class void_function_callback : public uvm_callback
{
friend class uvm_callback_agent;

protected:
    // Constructor: void_function_callback
    // Parameters:
    //  p_func   - function pointer to callback function
    //  arg1     - argument of callback function
    //  priority - priority of callback (0 - lowest priority)
    void_function_callback ( void (*p_func)(t_arg1) , t_arg1 arg1 , int priority = 0 ) :
        uvm_callback(priority),
        mp_func(p_func),
        _arg1(arg1) 
        { }; 

    // Destructor: void_function_callback
    virtual ~void_function_callback ( ) { };

    // Function: call
    //  Call function callback.
    void call ( ) 
    { 
        (* mp_func) ( _arg1 ); 
    }

protected:
    void (*mp_func)(t_arg1); 
    t_arg1 _arg1; 
}; 


//------------------------------------------------------------------------------
// Class: method_callback
//  class used for attaching prioritized callback methods 
//------------------------------------------------------------------------------
/*! \class method_callback
  \brief class used for attaching prioritized callback methods.

  
*/
template <typename t_return, 
	      class    t_class,
	      typename t_arg1 >
class method_callback : public uvm_callback
{
    friend class uvm_callback_agent;

protected:
    // Constructor: method_callback
    // Parameters:
    //  p_return - function callback return value
    //  t_class  - class instance of the method
    //  p_method - class method pointer to callback method
    //  arg1     - argument of callback function
    //  priority - priority of callback (0 - lowest priority)
    method_callback ( t_return * p_return , t_class * p_class, t_return (t_class::*p_method)(t_arg1), t_arg1 arg1 , int priority = 0 ) :
        uvm_callback(priority),
        mp_return(p_return),
        mp_class(p_class),
        mp_method(p_method),
        _arg1(arg1)
    { }; 
    
    // Destructor: method_callback
    virtual ~method_callback ( ) { }; 

    // Function: call
    //  Call function callback.
    void call ( ) 
    { 
        if ( mp_return ) 
        {
            * mp_return = ((*mp_class).*(mp_method))( _arg1 ); 
        } 
        else 
        {
            ((*mp_class).*(mp_method))( _arg1 ); 
        }
    }
protected:
    t_return* mp_return; 
    t_class*  mp_class;
    t_return  (t_class::*mp_method) ( t_arg1 );
    t_arg1    _arg1;
}; 


//------------------------------------------------------------------------------
// Class: void_method_callback
//  Class used for attaching prioritized callback methods 
//------------------------------------------------------------------------------
/*! \class void_method_callback
  \brief Class used for attaching prioritized callback methods.

  
*/
template <typename t_class,
	      typename t_arg1 >
class void_method_callback : public uvm_callback
{
    friend class uvm_callback_agent;

protected:
    // Constructor: void_method_callback
    // Parameters:
    //  t_class  - class instance of the method
    //  p_method - class method pointer to callback method
    //  arg1     - argument of callback function
    //  priority - priority of callback (0 - lowest priority)
    void_method_callback (t_class * p_class, void (t_class::*p_method)(t_arg1), t_arg1 arg1 , int priority = 0 ) :
        uvm_callback(priority),
        mp_class(p_class),
        mp_method(p_method),
        _arg1(arg1)
    { }; 

    // Destructor: void_method_callback
    virtual ~void_method_callback ( ) { }; 

    // Function: call
    //  Call function callback.
    void call ( ) { 
        ((*mp_class).*(mp_method))( _arg1 ); 
    }

protected:
    t_class* mp_class; 
    void     (t_class::*mp_method) ( t_arg1 ); 
    t_arg1   _arg1;
}; 

//------------------------------------------------------------------------------
// Class: void_method_callback
//  Maintains prioritized list of Event and Method uvm_callbacks, when derived 
//  from profiles template callback API
//------------------------------------------------------------------------------
/*! \class uvm_callback_agent
  \brief Maintains prioritized list of Event and Method uvm_callbacks, when derived 
//  from profiles template callback API.

  
*/
class  uvm_callback_agent
{
public:

    // Constructor: uvm_callback_agent
    uvm_callback_agent  ( ) :
        _p_callbacks(0) { };

    // Destructor: uvm_callback_agent
    ~uvm_callback_agent () 
    {
        if ( _p_callbacks ) 
        {
            uvm_callback_ptr_vector::iterator it     = _p_callbacks->begin();
            uvm_callback_ptr_vector::iterator end_it = _p_callbacks->end(); 

            for (; it != end_it; it++ ) 
            {
                delete *it; 
            }
            delete _p_callbacks; 
        }
    }
  
    // Function: call
    // Execute each call back in order of priority
    void call ( ) 
    {
        if ( _p_callbacks) 
        {
            for_each ( _p_callbacks->begin(), 
                       _p_callbacks->end(),
                    std::mem_fun ( &uvm_callback::call ) );  
        }
    }; 

    /*
    // Function: call
    // Execute each call back in order of priority
    void call_thread ( ) 
    {
        if ( _p_callbacks) 
        {
            for_each ( _p_callbacks->begin(), 
                       _p_callbacks->end(),
                    sc_spawn(sc_bind( &uvm_callback::call, this, "call" ) ) );  
        }
    }; 
    */


    // Function: register_function_callback
    //  Register a Function with Lowest Priority
    //
    // Parameters:
    //  p_func   - function pointer to callback function
    //  priority - priority of callback (0 - lowest priority)
    template <typename t_return,
              typename t_arg1 > 
    uvm_callback * register_function_callback ( t_return *p_return , t_return (*p_func)(t_arg1) , t_arg1 arg1 , int priority = 0 ) 
     {
         if ( _p_callbacks == 0 )  
             _p_callbacks = new uvm_callback_ptr_vector ( 0 ); 

         uvm_callback* reg_cb = new function_callback <t_return,t_arg1> ( p_return, p_func, arg1, priority );

         _p_callbacks->push_back (reg_cb);

         uvm_callback_by_priority callback_sorter;

         sort ( _p_callbacks->begin(),
                 _p_callbacks->end(),
                 callback_sorter );

         return reg_cb;
     }
  
    // Function: register_void_function_callback
    //  Register a void Function with Lowest Priority
    //
    // Parameters:
    //  p_func   - function pointer to callback function
    //  priority - priority of callback (0 - lowest priority)
    template < typename t_arg1 > 
    uvm_callback * register_void_function_callback ( void (*p_func)(t_arg1), t_arg1 arg1 , int priority = 0 ) 
    {
        if ( _p_callbacks == 0 ) 
            _p_callbacks = new uvm_callback_ptr_vector ( 0 ); 

        uvm_callback* reg_cb = new void_function_callback <t_arg1> ( p_func, arg1, priority );

        _p_callbacks->push_back(reg_cb);

        uvm_callback_by_priority callback_sorter;

        sort ( _p_callbacks->begin(),
                _p_callbacks->end(),
                callback_sorter );

        return reg_cb;
    }
  
    // Function: register_void_method_callback
    //  Register a member function with Lowest Priority
    //
    // Parameters:
    //  t_class  - class instance of the method
    //  p_method - class method pointer to callback method
    //  priority - priority of callback (0 - lowest priority)
    template <typename t_return,
              class t_class,
              typename t_arg1 > 
    uvm_callback * register_method_callback ( t_return * p_return , t_class * p_class, t_return (t_class::*p_method)(t_arg1), t_arg1 arg1 , int priority = 0 ) 
    {
        if ( _p_callbacks == 0 ) 
            _p_callbacks = new uvm_callback_ptr_vector ( 0 );

        uvm_callback* meth_cb = new method_callback <t_return,t_class,t_arg1> ( p_return, p_class, p_method, arg1, priority ); 

        _p_callbacks->push_back ( meth_cb );

        uvm_callback_by_priority callback_sorter;

        sort ( _p_callbacks->begin(),
                _p_callbacks->end(),
                callback_sorter );

        return meth_cb;
    }

    // Function: register_void_method_callback
    //  Register a void member function with Lowest Priority
    //
    // Parameters:
    //  t_class  - class instance of the method
    //  p_method - class method pointer to callback method
    //  priority - priority of callback (0 - lowest priority)
    //  type     - callback to register to (raise, drop, all drop)
    template <typename t_class,
              typename t_arg1 > 
    uvm_callback * register_void_method_callback (t_class * p_class, void (t_class::*p_method)(t_arg1), t_arg1 arg1 , int priority = 0 ) 
    {
        if ( _p_callbacks == 0 ) 
            _p_callbacks = new uvm_callback_ptr_vector ( 0 );

        uvm_callback * vmeth_cb = new void_method_callback <t_class,t_arg1> ( p_class, p_method, arg1, priority );

        _p_callbacks->push_back ( vmeth_cb );

        uvm_callback_by_priority callback_sorter;

        sort ( _p_callbacks->begin(),
                _p_callbacks->end(),
                callback_sorter );

        return vmeth_cb;
    }

    // Function: unregister
    //  Unregister a uvm_callback
    // 
    // Parameters:
    //  p_rem_callback - pointer to callback to be unregistered
    void unregister ( uvm_callback* p_rem_callback ) 
    {
        if ( _p_callbacks == 0 ) 
        {
            // TODO: error message
        }
        _p_callbacks->erase ( remove ( _p_callbacks->begin(), _p_callbacks->end(), p_rem_callback ) , _p_callbacks->end() ); // Remove it fromt callback list
        delete p_rem_callback;       // Delete it
    }

protected:

    uvm_callback_ptr_vector_ptr _p_callbacks;   // Vector of pointers to uvm_callback s sorted by priority 

};

//------------------------------------------------------------------------------
// Class: uvm_callback_by_priority
//  Sorter operation for priority callback
//------------------------------------------------------------------------------
/*! \class uvm_callback_by_priority
  \brief Sorter operation for priority callback.

  
*/
class uvm_callback_by_priority : public std::binary_function <uvm_callback*, uvm_callback*, bool>
{
public:
    bool operator() ( const uvm_callback* & lhs_value , 
            const uvm_callback* & rhs_value ) {
        if ( lhs_value->priority() == rhs_value->priority() ) { 
            return ( lhs_value < rhs_value );       
        } 
        return ( lhs_value->priority() < rhs_value->priority() ); 
    } 
};

}
#endif
