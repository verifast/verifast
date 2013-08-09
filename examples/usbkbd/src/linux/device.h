#ifndef _LINUX_DEVICE_H
#define _LINUX_DEVICE_H

struct device {
  struct device	*parent;
};

int dev_err(const struct device *dev, const char *fmt, ...);
  //@ requires false;
  //@ ensures true;

#endif
