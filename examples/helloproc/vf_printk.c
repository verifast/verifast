#include "vf_printk.h"
#include <linux/module.h>
void vf_printk(char *string){
	printk("%s", string);
}

