#ifndef _LINUX_HID_H
#define _LINUX_HID_H

// Not used anymore, the Linux API changed on this, causing the kernel
// module to compile on some Linux versions and not compile on some others.
// Of course, "everyone should just upgrade their kernel", but for me
// that's a no-go because the new kernel has a videodriver bug that
// makes my system unusable (https://bugs.freedesktop.org/show_bug.cgi?id=43123)
// so it should work both on old and new kernels. So we replaced err_hid
// by simple printk-calls.
//int err_hid(char *string);
//	//@ requires [?frac]chars(string, ?cs) &*& mem('\0', cs) == true &*& mem('%', cs) == false;
//	//@ ensures [frac]chars(string, cs);


#define USB_INTERFACE_CLASS_HID         3

#define USB_INTERFACE_SUBCLASS_BOOT     1

#define USB_INTERFACE_PROTOCOL_KEYBOARD 1
#define USB_INTERFACE_PROTOCOL_MOUSE    2

#endif
