#include "vf_procfs_impl.h"

/**
 * DOC - Linux' procfs callbacks are evil, so we use seq_file.
 *
 * There are multiple ways to "plug in" the code for reading/writing a
 * proc file.  Linux' procfs provides callbacks itself, both for
 * reading and writing.  These callbacks are set by filling in fields
 * of the struct proc_dir_entry after creating the proc entry, or by
 * calling the inline function create_proc_read_entry which does
 * exactly the same (and does not set the writing callback).
 *
 * So it is not possible to enforce that the file is not read before
 * the callback is set, when using Linux' procfs' callbacks.
 *
 * Somewhere hidden in the implementation of procfs (generic.c), it is
 * said that "seq_file" should be used instead of the procfs-callbacks
 * which are said to be legacy.  These legacy functions still exists
 * and are even not annotated/documented as legacy, it is unclear why.
 *
 * Besides procfs' callbacks, procfs also provides setting file
 * operations.  Implementing file operations is more complex, but
 * seq_file provides a wrapper which implements file operations and
 * provides a simple and easy to use API.
 * 
 * Setting file operations for a proc file can be done without having
 * a proc-file without callbacks for some time, by using
 * proc_create_data or proc_create.  The API also allows to do it
 * wrong (i.e. first creating the proc-file and then setting
 * callbacks).
 *
 * vf_procfs wraps around seq_file and procfs.
 * 
 * Writing is not supported: procfs-callbacks only supports it with a
 * race condition, and seq_file does not support it.  It could have
 * been supported by implementing file-operations for writing (like
 * seq_file does for reading).
 */


struct vf_procfs_dir *vf_procfs_mkdir(char *name)
{
	/*
	 * proc_mkdir copies the name right after its internal struct,
	 * so the user of this wrapper can keep the name after calling
	 * vf_procfs_mkdir.  The copy happens with memcpy in
	 * __proc_create.
	 */
	
	/*
	 * First kmalloc, then proc_mkdir.  Otherwise we could end
	 * up with an unwanted proc-directory after kmalloc failed.
	 */
	struct vf_procfs_dir *entry = vf_kmalloc(
					sizeof(struct vf_procfs_dir));
	if (entry == 0){
		return 0;
	}else{
		entry->proc = proc_mkdir(name, 0);
		if (entry->proc == 0){
			vf_kfree(entry);
			return 0;
		}else{
			return entry;
		}
	}
}


/**
 * vf_procfs_seq_show - called by seq_file when reading from the file.
 */
static int vf_procfs_seq_show(struct seq_file *s, void *v)
{
	struct vf_procfs_callback_handle cb_handle = {
		.seq_file = s
	};
	vf_procfs_read_callback_t *callback = s->private;
	if (callback(&cb_handle) == -1){
		return -ENOMEM;
	}else{
		return 0;
	}
}


/**
 * vf_procfs_seq_open - called by seq_file when opening the file.
 */
static int vf_procfs_seq_open(struct inode *inode, struct file *file)
{
	/*
	 * We get an inode and a file, so no custom data.  Based on
	 * the inode and/or the file, we must find a way to search
	 * which callback to call (there might be >1 callbacks), then
	 * we can put it as 3th parameter to single_open, such that
	 * vf_procfs_seq_show knows the callback and can call it.
	 * 
	 * The callback is stored in the data field of procfs' struct
	 * proc_dir_entry, and PDE(inode) gives us the proc_dir_entry.
	 *
	 * So we are directly accessing the data field of the struct,
	 * which is not optimal (where is the encapsulation?), but it
	 * is thread-safe since it's written before the callback can
	 * happen, and never rewritten afterwards (except some
	 * third-party evil extra kernel module, but we don't have
	 * control over that anyway).
	 */
	
	return single_open(file, vf_procfs_seq_show, PDE(inode)->data);
}


static struct file_operations vf_procfs_file_operations = {
	/*
	 * We are currently included with every module, if vf_procfs
	 * becomes a standalone module that export symbols, owner
	 * might (or might not) need to be changed.
	 */
	.owner   = THIS_MODULE, 
	
	.open    = vf_procfs_seq_open,
	
	/* Let seq_file handle these filesystem calls. */
	.read    = seq_read,
	.llseek  = seq_lseek,
	.release = seq_release
};


struct vf_procfs_file *vf_procfs_create_file(
			char *name, struct vf_procfs_dir *base,
			vf_procfs_read_callback_t *callback)
{
	
	/*
	 * proc_create_data copies the name, see vf_procfs_mkdir for
	 * more info.
	 */
	 
	struct proc_dir_entry *proc_entry ;
	
	/*
	 * Do the malloc first, otherwise we would have to destroy
	 * proc_entry if the malloc fails, and callbacks could already
	 * be running by then.
	 */
	struct vf_procfs_file *vf_procfs_file = vf_kmalloc(sizeof(
							struct vf_procfs_file));
	if (vf_procfs_file == 0){
		return 0;
	}
	
	/*
	 * 0444 = r--r--r--.  Write permission is off, write is
	 * currently not supported.
	 */
	proc_entry = proc_create_data(name, 0444, base->proc,
					&vf_procfs_file_operations, callback);
	
	/*
	 * We can't really do much after proc_create_data since
	 * callbacks could already be running while/before the very
	 * next line of code is executed.  Life would have been a lot
	 * easyer if setting up and then registering proc/seq entries
	 * would have been separated instead of combined in one call,
	 * but that's not the way the Linux API works.  Note that
	 * creating a proc entry with create_proc_entry and then
	 * setting its callbacks (via proc, not via seq) does not
	 * solve this problem since create_proc_entry already
	 * registers the proc entry (thus a proc entry without
	 * callback then exists for some time).
	 */
	if (proc_entry == 0){
		vf_kfree(vf_procfs_file);
		return 0;
	}
	vf_procfs_file->proc = proc_entry;
	
	return vf_procfs_file;
}


int vf_procfs_put_char(struct vf_procfs_callback_handle *cb_handle, char c)
{
	/*
	 * The backend works like this: (Linux' seq_file.c) seq_file
	 * has a counter and knows the size of its buffer.  The
	 * counter represents which byte is to be written (not which
	 * was the last byte written).  seq_putc returns 0
	 * ("no-error") when count < size (before writing).
	 * "Overflow" is detected (in seq_file's "traverse") when
	 * count == size.  So, when count == size-1, seq_putc will
	 * return 0, even though overflow will be detected.
	 * seq_putc's return code is pretty useless from a
	 * specification point of view because the error comes too
	 * late.
	 */
	return seq_putc(cb_handle->seq_file, c);
}


int vf_procfs_put_string(struct vf_procfs_callback_handle *cb_handle,
								char *string)
{
	return seq_puts(cb_handle->seq_file, string);
}


int vf_procfs_put_int(struct vf_procfs_callback_handle *cb_handle, int i)
{
	return seq_printf(cb_handle->seq_file, "%i", i);
}


bool vf_procfs_is_buffer_full(struct vf_procfs_callback_handle *cb_handle)
{
	char *buffp;
	return seq_get_buf(cb_handle->seq_file, &buffp) <= (size_t) 0;
}


void vf_procfs_rmdir(struct vf_procfs_dir *dir)
{
	remove_proc_entry(dir->proc->name, 0);
}


void vf_procfs_remove_file(struct vf_procfs_file *file,
					struct vf_procfs_dir *parent)
{
					
	/*
	 * remove_proc_entry waits for callbacks (here file operations
	 * via seq_file) to finish, search for "Wait until all
	 * existing callers into module are done" in proc/generic.c.
	 */
	remove_proc_entry(file->proc->name, parent->proc);
}

