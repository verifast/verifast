// linux/printk.h is introduced in 2.6.37, and it's useful if the module
// also compiles on older versions. So we skip this include here.
// printk definition will be included when kernel.h is #included.
// So we #include kernel.h.

//#include <linux/printk.h>

#include <linux/kernel.h>

