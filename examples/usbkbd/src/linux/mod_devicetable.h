#ifndef _LINUX_MOD_DEVICETABLE_H
#define _LINUX_MOD_DEVICETABLE_H

#include "../equals.h"


#define USB_DEVICE_ID_MATCH_VENDOR              0x0001
#define USB_DEVICE_ID_MATCH_PRODUCT             0x0002
#define USB_DEVICE_ID_MATCH_DEV_LO              0x0004
#define USB_DEVICE_ID_MATCH_DEV_HI              0x0008
#define USB_DEVICE_ID_MATCH_DEV_CLASS           0x0010
#define USB_DEVICE_ID_MATCH_DEV_SUBCLASS        0x0020
#define USB_DEVICE_ID_MATCH_DEV_PROTOCOL        0x0040
#define USB_DEVICE_ID_MATCH_INT_CLASS           0x0080
#define USB_DEVICE_ID_MATCH_INT_SUBCLASS        0x0100
#define USB_DEVICE_ID_MATCH_INT_PROTOCOL        0x0200

/**
 * For matching USB devices with modules, modules are associated with a table of usb_device_ids.
 */
struct usb_device_id {


	/* which fields to match against? */
	/*__u16*/ int		match_flags;

	/* Used for product specific matches; range is inclusive */
	 /*__u16*/ int		idVendor;
	 /*__u16*/ int		idProduct;
	// /*__u16*/ int		bcdDevice_lo;
	// /*__u16*/ int		bcdDevice_hi;

	/* Used for device class matches */
	/*__u8*/ int		bDeviceClass;
	// /*__u8*/ int		bDeviceSubClass;
	// /*__u8*/ int		bDeviceProtocol;

	/* Used for interface class matches */
	/*__u8*/ int		bInterfaceClass;
	/*__u8*/ int		bInterfaceSubClass;
	/*__u8*/ int		bInterfaceProtocol;

	/* not matched against */
	/*kernel_ulong_t*/ int	driver_info;
};

/*@
/*
 * A device driver might want to allocate an array of struct usb_device_id, but
 * to calculate the size of the array an integer overflow might happen.
 * Strictly spoken, we do not know if an integer overflow happens in e.g. 2*sizeof(struct usb_device_id),
 * even if the amount of items in the array is constant.
 * Indeed, the C standard does not put an upper bound on the padding introduced in
 * a struct, so it is possible sizeof(struct usb_device_id) is big enough to trigger an overflow when multiplied.
 * Implementations are typically insecure on this, i.e. they do not check when allocating an array of structs
 * whether the calculation of the amount of bytes to allocate overflows.
 * In other words, they rely on compiler assumptions.
 * We support this compiler assumption here for the struct usb_device_id,
 * but note that it is a compiler assumption and not specified by the C standard.
 */
lemma void sizeof_of_usb_device_id_is_low();
	requires true;
	ensures sizeof(struct usb_device_id) <= 8388608;
@*/

// isTerminating: whether this device id is a terminating entry in a device id table.
/*@ predicate usb_device_id(struct usb_device_id *usb_device_id, bool isTerminating) = 
	usb_device_id->match_flags |-> ?match_flags
	&*& usb_device_id->idVendor |-> ?idVendor
	&*& usb_device_id->idProduct |-> ?idProduct
	&*& usb_device_id->bDeviceClass |-> ?bDeviceClass
	&*& usb_device_id->bInterfaceClass |-> ?bInterfaceClass
	&*& usb_device_id->bInterfaceSubClass |-> ?bInterfaceSubClass
	&*& usb_device_id->bInterfaceProtocol |-> ?bInterfaceProtocol
	&*& usb_device_id->driver_info |-> ?driver_info
	// usb_match_id checks "id->idVendor || id->idProduct || id->bDeviceClass || id->bInterfaceClass || id->driver_info" (quoted),
	// so these fields _must_ be zero for a terminating entry.
	&*& isTerminating ?
		idVendor == 0
		&& idProduct == 0
		&& bDeviceClass == 0
		&& bInterfaceClass == 0
		&& driver_info == 0
	:
		idVendor != 0
		|| idProduct != 0
		|| bDeviceClass != 0
		|| bInterfaceClass != 0
		|| driver_info != 0
	;
@*/

/*@ predicate usb_device_id_table(int count, struct usb_device_id *usb_device_id) = 
	count == 0 ?
		usb_device_id(usb_device_id, true)
	:
		usb_device_id(usb_device_id, false)
		&*& usb_device_id_table(count-1, usb_device_id+1);
@*/

#endif

