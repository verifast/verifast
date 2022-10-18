#ifndef _LINUX_USB_INPUT_H
#define _LINUX_USB_INPUT_H

#include <linux/usb.h>
#include <linux/input.h>

static inline void
usb_to_input_id(const struct usb_device *dev, struct input_id *id);
  //@ requires usb_device(dev, ?ep0) &*& id->bustype |-> _ &*& id->vendor |-> _ &*& id->product |-> _ &*& id->version |-> _;
  //@ ensures usb_device(dev, ep0) &*& id->bustype |-> ?bustype &*& id->vendor |-> ?vendor &*& id->product |-> ?product &*& id->version |-> ?version;

#endif
