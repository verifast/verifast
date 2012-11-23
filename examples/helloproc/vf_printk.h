#ifndef VF_PRINTK_H
#define VF_PRINTK_H

void vf_printk(char *string);
	//@ requires [?frac]string(string, ?cs);
	//@ ensures [frac]string(string, cs);

#endif /* VF_PRINTK_H */
