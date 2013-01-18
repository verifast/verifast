KDIR := /lib/modules/$(shell uname -r)/build

# this name (in obj-m) can not be a filename, so choose a "new name". Otherwise it might fail annoyingly silently (!).
obj-m := usbkbd_verified_build.o
usbkbd_verified_build-objs := usbkbd_verified.o usbkbd_keycodes.o

obj-m := usbkbd_verified_build.o

PWD := $(shell pwd)



default: build

build:
	$(MAKE) -C $(KDIR) SUBDIRS=$(PWD) modules

clean:
	$(MAKE) -C $(KDIR) M=$(PWD) clean SUBDIRS=$(PWD)
	

