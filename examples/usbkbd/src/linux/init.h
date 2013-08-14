#ifndef _LINUX_INIT_H
#define _LINUX_INIT_H
/**
 * Specifications for init and exit callbacks of a kernel module.
 *
 * For sound verification, it must be ensured that the init and exit callbacks
 * of a module as specified in the C code, are the same ones as considered the
 * init and exit callbacks by the verifier.
 * This was done in the helloproc example.
 * To save time, we did not do this again because we already know it is possible
 * to do this.
 */


#include <linux/stddef.h>
//@ predicate_family module_state(module_setup_t setup, module_cleanup_t cleanup)();

/**
 * Instances are used to prove setup callback is a certain callback.
 *
 * In cleanup function, to close module_state(setup, cleanup), it has to
 * be proven that setup is the right setup  function. To do this,
 * you can use module_cleanup_callback_link by writing a predicate
 * family instance that constraints the value of setup.
 */ 
//@ predicate_family module_cleanup_callback_link(module_cleanup_t cleanup)(module_setup_t *setup);


/**
 * typedef int module_setup_t - Prototype of module initialisation function
 *
 * To be implemented by the programmer of the kernel module.
 *
 * In case of failure, the module must be returned (you are not
 * allowed to leak).  In case of success, you are supposed to put all
 * global data in module_state and/or callbacks, so you are not
 * allowed to return/ensure module(module, _).
 */
typedef int module_setup_t/*@(int module)@*/();
	//@ requires module(module, true) &*& not_in_interrupt_context(currentThread);
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& result == 0 ? // success
			module_state(this, ?cleanup)()
			&*& module_cleanup_callback_link(cleanup)(this)
		: // failure
			module(module, _)
		;
	@*/


typedef void module_cleanup_t/*@(int module)@*/();
	/*@ requires module_state(?setup, this)()
		&*& not_in_interrupt_context(currentThread)
		&*& module_cleanup_callback_link(this)(setup);
	@*/
	//@ ensures module(module, _) &*& not_in_interrupt_context(currentThread);

#endif
