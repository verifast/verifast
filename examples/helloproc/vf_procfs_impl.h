/**
 * DOC - vf_procfs_impl.h
 * 
 * This is implementation, it is not the API.
 */



#include "vf_procfs.h"
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/module.h>
#include <linux/errno.h>


struct vf_procfs_dir{
	struct proc_dir_entry *proc;
};


struct vf_procfs_file {
	struct proc_dir_entry *proc;
};


struct vf_procfs_callback_handle{
	struct seq_file *seq_file;
};

