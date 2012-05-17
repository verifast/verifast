#ifndef VF_INITEXIT_H
#define VF_INITEXIT_H

#include "vf_cleanup_debt.h"


/**
 * DOC - How to make initialisation of a kernel module both work and be
 *       verified?
 *
 * See vf_README.txt.
 */
 

/**
 * typedef int module_setup_t - Prototype of module initialisation function
 *
 * To be implemented by the user of this wrapper API.
 *
 * In case of failure, the module must be returned (you are not
 * allowed to leak).  In case of success, you are supposed to put all
 * global data in module_state and/or callbacks, so you are not
 * allowed to return/ensure module(module, _).
 *
 * Failure is interpreted as out of memory.  Other types of failure or
 * specific return codes are currently not supported.
 */
typedef int module_setup_t/*@(int module, void *module_cleanup_func)@*/();
	//@ requires module(module, true) &*& vf_cleanup_debt(0);
	/*@ ensures
		result == 0 ? // success
			[_]is_module_cleanup_t(module_cleanup_func, module, ?module_state)
			&*& module_state()
		: // failure
			module(module, _)
			&*& result == -1
			&*& vf_cleanup_debt(0);
	@*/


typedef void module_cleanup_t/*@(int module, predicate() module_state)@*/();
	//@ requires module_state();
	//@ ensures module(module, _) &*& vf_cleanup_debt(0);


#endif /* VF_INITEXIT_H */
