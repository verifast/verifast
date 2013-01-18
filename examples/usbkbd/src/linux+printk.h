#ifndef _LINUX_PRINTK_H
#define _LINUX_PRINTK_H

/**
 *
 * We don't support multiple arguments and formatted strings.
 */
int printk(char *string);
	// chars instead of array to support "string literals".
	//@ requires [?f]string(string, ?cs) &*& mem('%', cs) == false;
	//@ ensures [f]string(string, cs);

#endif
