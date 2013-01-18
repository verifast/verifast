#ifndef _LINUX_ERRNO_H
#define _LINUX_ERRNO_H


/* Values have to be filled in. Otherwise, wrong values will be assigned
 * to the enum fields, and an if (ENOENT == well_choosen_number){crash;}
 * can give other results in verification than in compilation.
 */
enum vf_errno {
	ECONNRESET = 104,
	ENOENT = 2,
	ESHUTDOWN = 108,
	ENODEV = 19,
	ENOMEM = 12,
	EIO = 5,
	EINPROGRESS = 115
};

#endif
