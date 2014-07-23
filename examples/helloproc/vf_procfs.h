#ifndef VF_PROCFS_H
#define VF_PROCFS_H

#include "vf_mem.h"
#include "include_ignored_by_verifast.h" // workaround, see inside file to read why.


#include "vf_cleanup_debt.h"

/**
 * struct vf_procfs_dir - a directory in /proc
 */
struct vf_procfs_dir;


/*#
 * predicate vf_procfs_dir - Represents a directory in the /proc-filesystem.
 * @nbFiles: number of files in this directory (a directory cannot
 *           contain subdirectories).
 *           Keep in mind we only keep track of files created with this
 *           vf_procfs API.
 */
/*@
predicate vf_procfs_dir(
	struct vf_procfs_dir *entry,
	list<char> name,
	int nbFiles);
@*/


/**
 * struct vf_procfs_file - a file in a directory in /proc
 */
struct vf_procfs_file;


/**
 * struct vf_procfs_callback_handle - see vf_procfs_put_char
 */
struct vf_procfs_callback_handle;


/*@
predicate vf_procfs_callback_handle(
	struct vf_procfs_callback_handle *cb_handle
);
@*/


/*@
predicate vf_procfs_file(
	struct vf_procfs_file *entry,
	list<char> name,
	struct vf_procfs_dir *parent,
	
	vf_procfs_read_callback_t *read_callback
);
@*/


/*# 
 * predicate_family vf_procfs_read_callback_data
 *
 * Create a predicate family instance for your callbacks.  This way,
 * your callbacks can have access to (mutexes for) global data.
 *
 * Do not include the predicate vf_procfs_file in the predicate_family
 * instance: vf_procfs_file makes it possible to remove the file.
 * Since removing the file waits for callbacks, this can cause
 * deadlock.  The current way kernel modules are verified does not
 * make this impossible
 */
/*@
predicate_family vf_procfs_read_callback_data(void *read_callback)();
@*/


/**
 * typedef vf_procfs_read_callback_t - callback: userspace reads
 *
 * Callback called when userspace reads a file.
 *
 * Returns -1 in case of not enough memory.
 */
typedef	int vf_procfs_read_callback_t(struct vf_procfs_callback_handle *cb_handle);
	/*@ requires
		// fractions are intentionally unspecified,
		// we don't know how many other threads have a fraction.
		[?fracData]vf_procfs_read_callback_data(this)()
		&*& [?fracHandle]vf_procfs_callback_handle(cb_handle)
		&*& vf_procfs_read_callback_buffer(cb_handle, nil, _);
	@*/
	/*@ ensures
		[fracData]vf_procfs_read_callback_data(this)()
		&*& [fracHandle]vf_procfs_callback_handle(cb_handle)
		&*& vf_procfs_read_callback_buffer(
			cb_handle,
			?fileContent,
			?isFullUnknown
		)
		&*& result == 0 || result == -1;
	@*/


/**
 * vf_procfs_mkdir - Creates an empty directory in /proc/.
 *
 * Subdirectories in directories in /proc/ are not possible with this
 * API.
 *
 * This function can fail for unspecified reasons, in that case 0 is
 * returned.
 */
struct vf_procfs_dir *vf_procfs_mkdir(char *name);
	/*@ requires
		[?frac]string(name, ?cs) 
		&*& mem('/', cs) == false
		// filename is not empty
		&*& cs != nil
		&*& vf_cleanup_debt(?debtCount);
	@*/
	/*@ ensures 
		[frac]string(name, cs)
		&*& result == 0 ? // failure
			vf_cleanup_debt(debtCount)
		: // success
			vf_procfs_dir(result, cs, 0)
			&*& vf_cleanup_debt(debtCount + 1);
	@*/


/**
 * vf_procfs_create_file - Creates a new proc file
 * 
 * According to this API, a proc file can not exist in the root
 * directory of /proc/.
 * 
 * This function can fail, e.g. when another file with the given name
 * already exists in the given parent directory or when there is not
 * enough free memory.  The full list of possible reasons for failure
 * is not specified.  In case of failure 0 is returned.
 */
struct vf_procfs_file *vf_procfs_create_file(char *name,
	struct vf_procfs_dir *parent, vf_procfs_read_callback_t *callback);
	/*@ requires
		[?frac]string(name, ?cs)
		&*& mem('/', cs) == false
		// filename is not empty
		&*& cs != nil
		&*& vf_procfs_dir(parent, ?parentName, ?nbFiles)
		&*& is_vf_procfs_read_callback_t(callback) == true
		&*& vf_procfs_read_callback_data(callback)()
		&*& vf_cleanup_debt(?debtCount);
	@*/
	/*@ ensures
		[frac]string(name, cs)
		&*& result == 0 ? // failure
			vf_procfs_dir(parent, parentName, nbFiles)
			&*& vf_procfs_read_callback_data(callback)()
			&*& vf_cleanup_debt(debtCount)
		: // success
			vf_procfs_dir(parent, parentName, nbFiles + 1)
			&*& vf_procfs_file(result, cs, parent, callback)
			&*& vf_cleanup_debt(debtCount + 1);
	@*/


/**
 * vf_procfs_remove_file - Removes a file.
 */
void vf_procfs_remove_file(struct vf_procfs_file *entry,
						struct vf_procfs_dir *parent);
	/*@ requires
		vf_procfs_file(entry, ?name, parent, ?callback)
		&*& vf_procfs_dir(parent, ?parentName, ?nbFiles)
		&*& vf_cleanup_debt(?debtCount);
	@*/
	/*@ ensures
		vf_procfs_dir(parent, parentName, nbFiles - 1)
		&*& vf_procfs_read_callback_data(callback)()
		&*& vf_cleanup_debt(debtCount - 1);
	@*/


/**
 * vf_procfs_rmdir - Removes the given empty directory.
 *
 * If files are created in the directory without the use of the
 * vf_procfs API by an unverified kernel module, the files of the
 * unverified module are leaked.  (Files of verified modules are thus
 * never leaked).
 */
void vf_procfs_rmdir(struct vf_procfs_dir *dir);
	/*@ requires
		vf_procfs_dir(dir, ?name, 0)
		&*& vf_cleanup_debt(?debtCount);
	@*/
	//@ ensures vf_cleanup_debt(debtCount - 1);


/*#
 * predicate vf_procfs_read_callback_buffer - see vf_procfs_put_char.
 */
/*
 * This is separated from vf_procfs_callback_handle for
 * modifiability/extensibility.  If e.g. write support is added,
 * predicate vf_procfs_write_callback_buffer can just be added,
 * instead of having lots of new arguments in
 * vf_procfs_callback_handle.
 */ 
/*@
predicate vf_procfs_read_callback_buffer(
	struct vf_procfs_callback_handle *cb_handle,
	list<char> contents,
	bool isFull);
@*/


/**
 * vf_procfs_put_char - Put a char in the virtual file
 * @handle: callbacks get a handle for a file, which should be passed to
 *          vf_procfs_put_*.
 * @c: char to put, after the previous data that has been put.
 *  
 * When the read callback is called, it needs a way to communicate
 * what the content of its file is, such that the content of the file
 * can be passed back to the userspace program that reads the file.
 * This function makes it possible for the read callback to
 * communicate the content of the file.
 *
 * Returns 0 on success or if the internal buffer becomes full but was
 * not full, and -1 if the internal buffer was already full.  If the
 * buffer is full when the callback ends, the callback will be called
 * again by the vf_procfs API with a bigger buffer if possible.
 * 
 * Note that we do not always know whether the buffer is full or not:
 * when "0" is returned, the buffer might have become full, or it
 * might not.  Also note that, when the buffer is full, the userspace
 * application that reads the file will not see the contents until a
 * callback call with a big enough buffer succeeds.  Since we don't
 * know if a big enough buffer will be available in memory, it is not
 * guaranteed that reading a file will ever succeed at all.
 *
 * If -1 is returned, the read callback can stop writing (i.e. calling
 * this function) and can just return (without error code).  vf_procfs
 * and its backend will see the buffer is full.
 *
 * If the buffer is full, the contents-argument of predicate
 * vf_procfs_read_callback_buffer is still updated.  This eases
 * writing API specifications.
 */
int vf_procfs_put_char(struct vf_procfs_callback_handle *cb_handle, char c);
	/*@ requires
		vf_procfs_read_callback_buffer(cb_handle, ?contents, ?isFull);
	@*/
	/*@ ensures
		isFull || result == -1 ?
			result == -1
			&*& vf_procfs_read_callback_buffer(
				cb_handle,
				append(contents, cons(c, nil)),
				true
			)
		:
			result == 0
			// We can not guarantee whether the buffer becomes
			// full with the new char.
			&*& vf_procfs_read_callback_buffer(
				cb_handle,
				append(contents, cons(c, nil)),
				_
			);
	@*/


/**
 * vf_procfs_put_string - like vf_procfs_put_char, but for strings.
 */
int vf_procfs_put_string(struct vf_procfs_callback_handle *cb_handle, char *string);
	/*@ requires
		vf_procfs_read_callback_buffer(cb_handle, ?contents, ?isFull)
		&*& [?frac]string(string, ?cs);
	@*/
	/*@ ensures
		[frac]string(string, cs)
		&*& isFull || result == -1 ?
			result == -1
			&*& vf_procfs_read_callback_buffer(
				cb_handle,
				append(contents, take(index_of('\0', cs), cs)),
				true
			)
		:
			result == 0
			&*& vf_procfs_read_callback_buffer(
				cb_handle,
				append(contents, take(index_of('\0', cs), cs)),
				_
			);
	@*/


/**
 * vf_procfs_put_int - like vf_procfs_put_char, but for ints.
 * 
 * The new content is currently unspecified.
 */
int vf_procfs_put_int(struct vf_procfs_callback_handle *cb_handle, int i);
	/*@ requires
		vf_procfs_read_callback_buffer(cb_handle, ?contents, ?isFull);
	@*/
	/*@ ensures
		isFull || result == -1 ?
			result == -1
			&*& vf_procfs_read_callback_buffer(
				cb_handle,
				?newContents,
				true
			)
			
		:
			result == 0
			&*& vf_procfs_read_callback_buffer(
				cb_handle,
				?newContents,
				_
			);
	@*/


/**
 * vf_procfs_is_buffer_full - returns wether the internal buffer is full.
 *
 * See vf_procfs_put_char.
 */
bool vf_procfs_is_buffer_full(struct vf_procfs_callback_handle *cb_handle);
	/*@ requires
		vf_procfs_read_callback_buffer(cb_handle, ?contents, ?isFull);
	@*/
	/*@ ensures
		vf_procfs_read_callback_buffer(cb_handle, contents, isFull)
		&*& result == isFull;
	@*/

#endif /* VF_PROCFS_H */
