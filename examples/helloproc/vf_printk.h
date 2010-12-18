#ifndef VF_PRINTK_H
#define VF_PRINTK_H

void vf_printk(char *string);
	//@ requires [?frac]chars(string, ?cs) &*& mem('\0', cs) == true;
	//@ ensures [frac]chars(string, cs);

#endif /* VF_PRINTK_H */
