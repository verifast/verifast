/**
 * DOC: Helloproc
 *
 * Helloproc is an example verified kernel module.
 * It uses the wrapper of VeriFast Linux Kernel Module Verification Kit API
 * for interaction with the Linux kernel.
 *
 * Helloproc creates a virtual file /proc/helloproc/value
 * which contains a text, including the number of times
 * the file is read.
 *
 */

#include "vf_printk.h"
#include "vf_initexit.h"
#include "vf_mem.h"
#include "vf_procfs.h"
#include "vf_mutex.h"
#include "limits.h"


/*---- Callback data ----*/
static int counter; /* How many times has the file been read? */
static struct vf_mutex *mutex;


/*---- Initexit data ----*/
static struct vf_procfs_dir *dir;
static struct vf_procfs_file *file;


/*@
predicate callback_data_mutexed() = 
	integer(&counter, ?counter_ptr);
@*/


/*@
predicate_family_instance
	vf_procfs_read_callback_data(read_proc_callback)() =
	
	mutex |-> ?mutex_ptr
	&*& vf_mutex(mutex_ptr, callback_data_mutexed);
@*/


/*@
predicate module_state() =
	dir |-> ?dir_ptr
	&*& vf_procfs_dir(
		dir_ptr,
		cons(
			'h',
			cons('e',
			cons('l',
			cons('l',
			cons('o',
			cons('p',
			cons('r',
			cons('o',
			cons('c',
			nil))))))))
		)
		, 1
	)
	&*& file |-> ?file_ptr
	&*& vf_procfs_file(
		file_ptr,
		cons(
			'v',
			cons('a',
			cons('l',
			cons('u',
			cons('e',
			nil))))
		),
		dir_ptr, 
		read_proc_callback
	)
	&*& vf_cleanup_debt(
		1  // dir
		+1 // file
		+1 // mutex
	);
@*/


/**
 * read_proc_callback - Callback called when userspace reads the file.
 */
int read_proc_callback(struct vf_procfs_callback_handle *cb_handle)
	//@ : vf_procfs_read_callback_t
	/*@ requires
		[?fracData]vf_procfs_read_callback_data(
						read_proc_callback)()
		&*& [?fracHandle]vf_procfs_callback_handle(cb_handle)
		&*& vf_procfs_read_callback_buffer(cb_handle, nil, _);
	@*/
	/*@ ensures
		[fracData]vf_procfs_read_callback_data(
						read_proc_callback)()
		&*& [fracHandle]vf_procfs_callback_handle(cb_handle)
		
		&*& vf_procfs_read_callback_buffer(cb_handle,
			?cs,
			?isFullUnknown)
		
		// we never run out of memory (no kmalloc used, also
		// not indirectly).
		&*& result == 0;
		
		// File contents currently does not have formal specifications.
	@*/
{
	int counter_backup;
	
	vf_procfs_put_string(cb_handle, "This is helloproc.\n");
	vf_procfs_put_string(cb_handle, "This file is read ");
	
	//@ open [fracData]vf_procfs_read_callback_data(read_proc_callback)();
	
	vf_mutex_lock(mutex);
	//@ open callback_data_mutexed();
	counter_backup = counter;
	if (counter < INT_MAX){
		//@ produce_limits(counter);
		counter++;
	}else{
		vf_procfs_put_string(cb_handle, "more than ");
	}

	vf_procfs_put_int(cb_handle, counter);
	
	vf_procfs_put_string(cb_handle, " times.\n");
	
	if (vf_procfs_is_buffer_full(cb_handle)){
		counter = counter_backup;
	}
	
	//@ close callback_data_mutexed();
	vf_mutex_unlock(mutex);

	//@ close [fracData]vf_procfs_read_callback_data(read_proc_callback)();
	
	return 0;
}


/**
 * helloproc_main_module_init - Initialisation of the kernel module.
 * 
 * Called when this module is loaded.
 */
int helloproc_main_module_init() //@ : module_setup_t(helloproc_main, helloproc_main_module_exit)
	//@ requires module(helloproc_main, true) &*& vf_cleanup_debt(0);
	/*@ ensures
		result == 0 ?
			[_]is_module_cleanup_t(helloproc_main_module_exit, helloproc_main, module_state)
			&*& module_state()
		:
			module(helloproc_main, _)
			&*& result == -1
			&*& vf_cleanup_debt(0);
	@*/
{

	//@ open_module();
	
	/*---- Create dir ----*/
	dir = vf_procfs_mkdir("helloproc");
	if (dir == 0){
		goto error_mkdir;
	}
	
	/*---- Initialize mutexed data ----*/
	counter = 0;
	
	/*---- Create mutex ----*/
	//@ close callback_data_mutexed();
	//@ close vf_mutex_create_ghost_arg(callback_data_mutexed);
	mutex = vf_mutex_create();
	if (mutex == 0){
		goto error_mutex;
	}
		
	/*---- Create file ----*/
	//@ close vf_procfs_read_callback_data(read_proc_callback)();
	file = vf_procfs_create_file("value", dir, read_proc_callback);
	if (file == 0){
		goto error_file;
	}
	
	/*---- We're done ----*/
	//@ produce_function_pointer_chunk module_cleanup_t(helloproc_main_module_exit)(helloproc_main, module_state)() { call(); }
	//@ close module_state();
	return 0;
	
	
	/*---- Errors ----*/
	/**
	 * DOC - Why the gotos? Aren't gotos evil?
	 *
	 * We use gotos to avoid code duplication because code
	 * duplication is evil.  "goto error_file;" jumps to
	 * "error_file:" but also executes "error_mutex:" etc.  This
	 * way the code of "error_mutex" only needs to be written
	 * once, which would not be the case with if-then-else (except
	 * when using extra flags).  This pattern is commonly used in
	 * the Linux kernel, so we're actually just adapting our code
	 * style to the Linux kernel's style.
	 */
	
error_file:
	//@ open vf_procfs_read_callback_data(read_proc_callback)();
	vf_mutex_dispose(mutex);
	
error_mutex:
	//@ open callback_data_mutexed();
	vf_procfs_rmdir(dir);
	
error_mkdir:
	//@ close_module();
	return -1;
}


/**
 * helloproc_main_module_exit - Cleanup of kernel module.
 *
 * Called when this kernel module is being unloaded.
 */
void helloproc_main_module_exit()
	//@ requires module_state();
	//@ ensures module(helloproc_main, _) &*& vf_cleanup_debt(0);
{
	
	//@ open module_state();
	
	
	/*---- Dispose file ----*/
	vf_procfs_remove_file(file, dir);
	//@ open vf_procfs_read_callback_data(read_proc_callback)();
	
	/*----  Dispose mutex ----*/
	vf_mutex_dispose(mutex);
	//@ open callback_data_mutexed();
	
	/*----  Dispose dir ----*/
	vf_procfs_rmdir(dir);
	

	//@ close_module();	
	vf_printk("Helloproc module: unloaded.\n");
}

